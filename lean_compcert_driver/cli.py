from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

from lean_compcert_probe.probe import run_probe

from . import __version__
from .manifest import runtime_hash, write_build_manifest
from .runtime_check import check_runtime


def _root() -> Path:
    return Path(__file__).resolve().parent.parent


def _common_options(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--ccomp", default="ccomp")
    parser.add_argument("--target")
    parser.add_argument(
        "--profile", choices=("portable", "hosted", "strict"), default="portable"
    )
    parser.add_argument(
        "--runtime", choices=("hybrid", "compcert", "strict"), default="hybrid"
    )
    parser.add_argument("--output", "--emit-c", dest="output", type=Path)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--keep-temporaries", action="store_true")
    parser.add_argument("--debug-symbols", action="store_true")
    parser.add_argument("--opt-level", choices=("0", "1", "2"), default="1")
    parser.add_argument("--reject-unsafe", action="store_true")
    parser.add_argument(
        "--expected-runtime-abi-hash",
        help="reject the build unless the active Lean/runtime ABI has this SHA-256",
    )
    parser.add_argument("--report", type=Path)


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        prog="lean-compcert",
        description="Compile Lean-generated application code with CompCert.",
    )
    result.add_argument("--version", action="version", version=__version__)
    commands = result.add_subparsers(dest="command", required=True)

    build = commands.add_parser("build", help="build and differentially run a Lean module")
    build.add_argument("input", type=Path)
    build.add_argument("--no-differential-check", action="store_true")
    build.add_argument("--run-arg", action="append", default=[])
    _common_options(build)

    emit = commands.add_parser("emit-c", help="emit normalized CompCert-compatible C")
    emit.add_argument("input", type=Path)
    _common_options(emit)

    compile_ir = commands.add_parser(
        "compile-ir", help="capture Lean impure LCNF and lower compatible declarations"
    )
    compile_ir.add_argument("input", type=Path)
    compile_ir.add_argument(
        "--output", "--emit-lowered-ir", dest="output", type=Path
    )
    compile_ir.add_argument("--ccomp", default="ccomp")
    compile_ir.add_argument("--target")
    compile_ir.add_argument("--opt-level", choices=("0", "1", "2"), default="1")
    compile_ir.add_argument("--debug-symbols", action="store_true")
    compile_ir.add_argument("--timeout", type=float, default=120)

    runtime = commands.add_parser(
        "check-runtime", help="scan runtime sources with CompCert"
    )
    runtime.add_argument("--ccomp", default="ccomp")
    runtime.add_argument("--target")
    runtime.add_argument("--output", type=Path)
    runtime.add_argument("--timeout", type=float, default=120)

    doctor = commands.add_parser("doctor", help="check required tools and versions")
    doctor.add_argument("--ccomp", default="ccomp")
    return result


def _validate_mode(profile: str, runtime: str) -> str | None:
    if (profile == "strict") != (runtime == "strict"):
        return "strict profile and strict runtime mode must be selected together"
    if runtime != "hybrid":
        return (
            f"runtime mode `{runtime}` is not complete; use `hybrid` for the "
            "current executable backend"
        )
    return None


def _build_or_emit(args: argparse.Namespace, differential: bool) -> int:
    if not args.input.is_file():
        print(f"error: input does not exist: {args.input}", file=sys.stderr)
        return 2
    if error := _validate_mode(args.profile, args.runtime):
        print(f"error: {error}", file=sys.stderr)
        return 2
    active_runtime_hash = runtime_hash(_root())
    if (
        args.expected_runtime_abi_hash
        and args.expected_runtime_abi_hash != active_runtime_hash
    ):
        print(
            "error: runtime ABI hash mismatch: "
            f"expected {args.expected_runtime_abi_hash}, got {active_runtime_hash}",
            file=sys.stderr,
        )
        return 1
    if args.reject_unsafe:
        source_text = args.input.read_text(encoding="utf-8")
        if re.search(r"\bunsafe\b", source_text):
            print(
                f"error: `{args.input}` contains an unsafe declaration and --reject-unsafe is active",
                file=sys.stderr,
            )
            return 1
    output = args.output or (
        Path(".lake") / "build" / "lean-compcert" / args.input.stem
    )
    report = run_probe(
        source=args.input,
        output=output,
        ccomp=args.ccomp,
        target=args.target,
        timeout=args.timeout,
        attempt_rewrites=True,
        debug_symbols=args.debug_symbols,
        opt_level=args.opt_level,
        differential_check=differential,
        run_args=tuple(getattr(args, "run_arg", [])),
    )
    manifest_path = args.report or (output / "build-manifest.json")
    write_build_manifest(_root(), report, manifest_path, args.profile, args.runtime)
    if report.status != "compatible":
        print(f"{report.status}: {output / 'report.md'}", file=sys.stderr)
        return 1
    candidate = output.resolve() / f"{args.input.stem}.compcert"
    print(f"compatible C: {report.compcert_compiled[-1]}")
    if candidate.is_file():
        print(f"executable: {candidate}")
    print(f"manifest: {manifest_path}")
    return 0


def _insert_capture_import(source: str) -> str:
    capture_import = "import LeanCompCert.CompilerAdapter.Pass\n"
    if source.startswith("module ") or source.startswith("module\n"):
        newline = source.find("\n")
        if newline >= 0:
            return source[: newline + 1] + capture_import + source[newline + 1 :]
    return capture_import + source


def _compile_ir(args: argparse.Namespace) -> int:
    if not args.input.is_file():
        print(f"error: input does not exist: {args.input}", file=sys.stderr)
        return 2
    root = _root()
    output = (
        args.output or Path(".lake") / "build" / "lean-compcert-ir" / args.input.stem
    ).resolve()
    views = output / "views"
    generated_c = output / "c"
    output.mkdir(parents=True, exist_ok=True)
    views.mkdir(parents=True, exist_ok=True)
    generated_c.mkdir(parents=True, exist_ok=True)
    for pattern, directory in (
        ("*.lcnfview", views),
        ("*.c", generated_c),
        ("*.error", generated_c),
    ):
        for stale in directory.glob(pattern):
            stale.unlink()
    derived = output / "Captured.lean"
    derived.write_text(
        _insert_capture_import(args.input.read_text(encoding="utf-8")),
        encoding="utf-8",
    )
    build = subprocess.run(
        ["lake", "build", "LeanCompCert.CompilerAdapter.Pass"],
        cwd=root,
        check=False,
    )
    if build.returncode != 0:
        return build.returncode
    environment = os.environ.copy()
    environment["LEAN_COMPCERT_LCNF_DIR"] = str(views)
    environment["LEAN_COMPCERT_C_DIR"] = str(generated_c)
    command = [
        "lake",
        "env",
        "lean",
        "-R",
        str(output),
        "-o",
        str(output / f"{args.input.stem}.olean"),
        "-i",
        str(output / f"{args.input.stem}.ilean"),
        "-c",
        str(output / f"{args.input.stem}.lean.c"),
        str(derived),
    ]
    completed = subprocess.run(command, cwd=root, env=environment, check=False)
    if completed.returncode != 0:
        return completed.returncode
    view_files = sorted(views.glob("*.lcnfview"))
    c_files = sorted(generated_c.glob("*.c"))
    error_files = sorted(generated_c.glob("*.error"))
    compiler = shutil.which(args.ccomp)
    if compiler is None and Path(args.ccomp).is_file():
        compiler = str(Path(args.ccomp).resolve())
    compcert_results: list[dict[str, object]] = []
    if compiler is not None:
        objects = output / "objects"
        objects.mkdir(exist_ok=True)
        for stale in objects.glob("*.o"):
            stale.unlink()
        lean_prefix = subprocess.run(
            ["lean", "--print-prefix"],
            text=True,
            stdout=subprocess.PIPE,
            check=False,
        )
        include_args = ["-I", str(root / "runtime" / "include")]
        if lean_prefix.returncode == 0:
            include_args += [
                "-I", str(Path(lean_prefix.stdout.strip()) / "include")
            ]
        for source in c_files:
            object_file = objects / f"{source.stem}.o"
            command = [
                compiler,
                *(["-target", args.target] if args.target else []),
                *include_args,
                f"-O{args.opt_level}",
                *(["-g"] if args.debug_symbols else []),
                "-c",
                str(source),
                "-o",
                str(object_file),
            ]
            try:
                compiled = subprocess.run(
                    command,
                    cwd=root,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=args.timeout,
                    check=False,
                )
                compcert_results.append(
                    {
                        "source": str(source),
                        "object": str(object_file),
                        "command": command,
                        "exitCode": compiled.returncode,
                        "diagnostic": compiled.stderr.strip(),
                    }
                )
            except subprocess.TimeoutExpired:
                compcert_results.append(
                    {
                        "source": str(source),
                        "object": str(object_file),
                        "command": command,
                        "exitCode": None,
                        "diagnostic": f"timed out after {args.timeout} seconds",
                    }
                )
    version = subprocess.run(
        ["lean", "--version"],
        text=True,
        stdout=subprocess.PIPE,
        check=False,
    ).stdout.strip()
    summary = {
        "input": str(args.input),
        "compilerVersion": version,
        "stableViews": [str(path) for path in view_files],
        "loweredC": [str(path) for path in c_files],
        "compCertCompiler": compiler,
        "compCertResults": compcert_results,
        "rejected": [
            {"file": str(path), "diagnostic": path.read_text(encoding="utf-8").strip()}
            for path in error_files
        ],
    }
    report_path = output / "compile-ir-report.json"
    report_path.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        f"captured {len(view_files)} declarations; lowered {len(c_files)}; "
        f"CompCert-compiled "
        f"{sum(result['exitCode'] == 0 for result in compcert_results)}; "
        f"rejected {len(error_files)}"
    )
    print(f"report: {report_path}")
    all_compiled = (
        compiler is not None
        and len(compcert_results) == len(c_files)
        and all(result["exitCode"] == 0 for result in compcert_results)
    )
    return 0 if c_files and all_compiled else 1


def _doctor(args: argparse.Namespace) -> int:
    tools = {
        "lean": shutil.which("lean"),
        "lake": shutil.which("lake"),
        "ccomp": shutil.which(args.ccomp),
        "python3": shutil.which("python3"),
    }
    healthy = True
    print(f"lean-compcert {__version__}")
    for name, path in tools.items():
        if path is None:
            healthy = False
            print(f"{name}: missing")
            continue
        version_arg = "-version" if name == "ccomp" else "--version"
        completed = subprocess.run(
            [path, version_arg],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        first_line = completed.stdout.strip().splitlines()
        print(f"{name}: {path} ({first_line[0] if first_line else 'available'})")
    runtime_files = (
        _root() / "runtime" / "include" / "stdatomic.h",
        _root() / "runtime" / "adapters" / "atomics.c",
        _root() / "runtime" / "inventory.yaml",
    )
    for path in runtime_files:
        if not path.is_file():
            healthy = False
            print(f"runtime: missing {path}")
    return 0 if healthy else 1


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    if args.command == "build":
        return _build_or_emit(args, not args.no_differential_check)
    if args.command == "emit-c":
        return _build_or_emit(args, False)
    if args.command == "compile-ir":
        return _compile_ir(args)
    if args.command == "check-runtime":
        output = args.output or Path(".lake") / "build" / "lean-compcert-runtime"
        compatible, _ = check_runtime(
            _root(), output.resolve(), args.ccomp, args.target, args.timeout
        )
        print(f"report: {output / 'runtime-compatibility.json'}")
        return 0 if compatible else 1
    if args.command == "doctor":
        return _doctor(args)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
