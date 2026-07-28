from __future__ import annotations

import os
import platform
import shlex
import shutil
from dataclasses import replace
from pathlib import Path

from . import __version__
from .classify import classify_failure, minimize_diagnostics
from .model import CommandResult, FailureClass, ProbeReport
from .process import run_command
from .report import write_json, write_markdown
from .rewrite import mechanical_rewrite

_PACKAGE_ROOT = Path(__file__).resolve().parent.parent


def _effective_target(target: str | None) -> str:
    if target:
        return target
    machine = platform.machine() or "unknown"
    system = platform.system().lower() or "unknown"
    return f"{machine}-{system} (ccomp default; host-inferred)"


def _project_root(source: Path) -> Path:
    for candidate in (source.parent, *source.parents):
        if any((candidate / marker).exists() for marker in ("lakefile.toml", "lakefile.lean")):
            return candidate
    return source.parent


def _lean_command(root: Path, executable: str) -> list[str]:
    if (root / "lakefile.toml").exists() or (root / "lakefile.lean").exists():
        lake = shutil.which("lake")
        if lake:
            return [lake, "env", executable]
    return [executable]


def _version(
    stage: str, command: list[str], root: Path, timeout: float
) -> tuple[str | None, CommandResult]:
    result = run_command(stage, command, root, timeout)
    value = (result.stdout or result.stderr).strip().splitlines()
    return (value[0] if result.succeeded and value else None, result)


def _record(report: ProbeReport, result: CommandResult) -> CommandResult:
    if result.succeeded:
        report.commands.append(result)
        return result
    category = (
        FailureClass.TOOL_UNAVAILABLE
        if result.exit_code is None and "timed out" not in result.stderr
        else classify_failure(result.stderr, result.stage)
    )
    classified = replace(result, classification=category)
    report.commands.append(classified)
    messages = minimize_diagnostics(result.stderr or result.stdout)
    report.failures.setdefault(category.value, [])
    for message in messages:
        if message not in report.failures[category.value]:
            report.failures[category.value].append(message)
    return classified


def _compare_runs(
    report: ProbeReport,
    root: Path,
    reference_command: str,
    candidate_command: str,
    timeout: float,
) -> None:
    _compare_argv(
        report,
        root,
        shlex.split(reference_command),
        shlex.split(candidate_command),
        timeout,
    )


def _compare_argv(
    report: ProbeReport,
    root: Path,
    reference_command: list[str],
    candidate_command: list[str],
    timeout: float,
) -> None:
    reference = run_command(
        "run-reference", reference_command, root, timeout
    )
    candidate = run_command(
        "run-compcert", candidate_command, root, timeout
    )
    # A program's nonzero exit status is observable behavior, not itself a probe
    # failure. Only failure to launch/timeout or a behavioral mismatch is an error.
    for result in (reference, candidate):
        if result.exit_code is None:
            _record(report, result)
        else:
            report.commands.append(result)
    if reference.exit_code is not None and candidate.exit_code is not None:
        report.differential_match = (
            reference.exit_code == candidate.exit_code
            and reference.stdout == candidate.stdout
            and reference.stderr == candidate.stderr
        )
        if not report.differential_match:
            report.failures.setdefault("differential mismatch", []).append(
                "stdout, stderr, or exit status differed"
            )


def run_probe(
    source: Path,
    output: Path,
    lean: str = "lean",
    ccomp: str = "ccomp",
    target: str | None = None,
    timeout: float = 120,
    attempt_rewrites: bool = False,
    debug_symbols: bool = False,
    opt_level: str = "1",
    differential_check: bool = False,
    run_args: tuple[str, ...] = (),
    reference_command: str | None = None,
    candidate_command: str | None = None,
) -> ProbeReport:
    source = source.resolve()
    root = _project_root(source)
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    generated = output / f"{source.stem}.lean.c"

    report = ProbeReport(
        schema_version=1,
        backend_version=__version__,
        input=os.path.relpath(source, root),
        output_directory=os.path.relpath(output, root),
        lean_version=None,
        lean_git_revision=None,
        compcert_version=None,
        compcert_target=_effective_target(target),
    )

    lean_prefix = _lean_command(root, lean)
    lean_version, lean_version_result = _version(
        "lean-version", [*lean_prefix, "--version"], root, timeout
    )
    _record(report, lean_version_result)
    report.lean_version = lean_version
    revision_result = _record(
        report, run_command("lean-revision", [*lean_prefix, "-g"], root, timeout)
    )
    if revision_result.succeeded:
        report.lean_git_revision = revision_result.stdout.strip() or None

    ccomp_path = shutil.which(ccomp)
    if ccomp_path is None and Path(ccomp).is_file():
        ccomp_path = str(Path(ccomp).resolve())
    if ccomp_path is None:
        _record(
            report,
            CommandResult(
                stage="compcert-version",
                command=[ccomp, "-version"],
                exit_code=None,
                stdout="",
                stderr=f"CompCert compiler not found: {ccomp}",
                duration_ms=0,
            ),
        )
    else:
        compcert_version, compcert_version_result = _version(
            "compcert-version", [ccomp_path, "-version"], root, timeout
        )
        _record(report, compcert_version_result)
        report.compcert_version = compcert_version

    emission_result = run_command(
        "lean-emission",
        [*lean_prefix, "-c", str(generated), str(source)],
        root,
        timeout,
    )
    if emission_result.succeeded and not generated.is_file():
        emission_result = replace(
            emission_result,
            exit_code=1,
            stderr=f"Lean reported success but did not create generated C: {generated}",
        )
    emission = _record(report, emission_result)
    if emission.succeeded and generated.exists():
        report.generated_c.append(os.path.relpath(generated, root))

    probe_source = generated
    if emission.succeeded and attempt_rewrites:
        rewrite = mechanical_rewrite(generated.read_text(encoding="utf-8"))
        if rewrite.applied:
            probe_source = output / f"{source.stem}.rewritten.c"
            probe_source.write_text(rewrite.text, encoding="utf-8")
            report.rewritten_c.append(os.path.relpath(probe_source, root))

    lean_install_prefix: Path | None = None
    if emission.succeeded and (ccomp_path is not None or differential_check):
        lean_prefix_result = _record(
            report,
            run_command("lean-prefix", [*lean_prefix, "--print-prefix"], root, timeout),
        )
        include_args: list[str] = []
        if lean_prefix_result.succeeded:
            prefix = lean_prefix_result.stdout.strip()
            if prefix:
                lean_install_prefix = Path(prefix)
                include_args = ["-I", str(lean_install_prefix / "include")]

    standard_executable: Path | None = None
    if emission.succeeded and differential_check and lean_install_prefix is not None:
        leanc = lean_install_prefix / "bin" / "leanc"
        standard_object = output / f"{source.stem}.standard.o"
        standard_output = output / f"{source.stem}.standard"
        standard_compile = _record(
            report,
            run_command(
                "standard-compile",
                [str(leanc), "-c", "-o", str(standard_object), str(generated)],
                root,
                timeout,
            ),
        )
        if standard_compile.succeeded:
            report.reference_artifacts.append(
                os.path.relpath(generated, root)
            )
            standard_link = _record(
                report,
                run_command(
                    "link-reference",
                    [str(leanc), "-o", str(standard_output), str(standard_object)],
                    root,
                    timeout,
                ),
            )
            if standard_link.succeeded:
                standard_executable = standard_output

    candidate_executable: Path | None = None
    if emission.succeeded and ccomp_path is not None:
        include_args = ["-I", str(_PACKAGE_ROOT / "runtime" / "include")]
        if lean_install_prefix is not None:
            include_args.extend(["-I", str(lean_install_prefix / "include")])
        target_args = ["-target", target] if target else []
        compile_args = [f"-O{opt_level}"]
        if debug_symbols:
            compile_args.append("-g")
        preprocessed = output / f"{source.stem}.i"
        preprocessing = _record(
            report,
            run_command(
                "compcert-preprocess",
                [
                    ccomp_path,
                    *target_args,
                    *include_args,
                    "-E",
                    str(probe_source),
                    "-o",
                    str(preprocessed),
                ],
                root,
                timeout,
            ),
        )
        if preprocessing.succeeded:
            object_file = output / f"{source.stem}.o"
            compilation = _record(
                report,
                run_command(
                    "compcert-compile",
                    [
                        ccomp_path,
                        *target_args,
                        *include_args,
                        *compile_args,
                        "-c",
                        str(probe_source),
                        "-o",
                        str(object_file),
                    ],
                    root,
                    timeout,
                ),
            )
            if compilation.succeeded:
                report.compcert_compiled.append(os.path.relpath(probe_source, root))
            if (
                compilation.succeeded
                and differential_check
                and lean_install_prefix is not None
            ):
                leanc = lean_install_prefix / "bin" / "leanc"
                adapter_source = _PACKAGE_ROOT / "runtime" / "adapters" / "atomics.c"
                adapter_object = output / "lean_compcert_atomics.adapter.o"
                adapter_compile = _record(
                    report,
                    run_command(
                        "adapter-compile",
                        [
                            str(leanc),
                            "-c",
                            "-o",
                            str(adapter_object),
                            str(adapter_source),
                        ],
                        root,
                        timeout,
                    ),
                )
                candidate_executable = output / f"{source.stem}.compcert"
                if adapter_compile.succeeded:
                    report.conventionally_compiled.append(
                        os.path.relpath(adapter_source, root)
                    )
                    candidate_link = _record(
                        report,
                        run_command(
                            "link-compcert",
                            [
                                str(leanc),
                                "-o",
                                str(candidate_executable),
                                str(object_file),
                                str(adapter_object),
                            ],
                            root,
                            timeout,
                        ),
                    )
                    if candidate_link.succeeded:
                        report.external_components.extend(
                            [
                                "prebuilt Lean runtime",
                                "assembler and linker invoked by leanc",
                                "system libraries",
                            ]
                        )
                    else:
                        candidate_executable = None
                else:
                    candidate_executable = None

    if differential_check:
        if standard_executable is not None and candidate_executable is not None:
            _compare_argv(
                report,
                root,
                [str(standard_executable), *run_args],
                [str(candidate_executable), *run_args],
                timeout,
            )
        elif emission.succeeded and ccomp_path is not None:
            report.failures.setdefault("differential check incomplete", []).append(
                "one or both native executables could not be built"
            )

    if reference_command or candidate_command:
        if reference_command and candidate_command:
            _compare_runs(report, root, reference_command, candidate_command, timeout)
        else:
            report.failures.setdefault("configuration", []).append(
                "--reference-command and --candidate-command must be supplied together"
            )

    meaningful_failures = {
        key: value
        for key, value in report.failures.items()
        if key != FailureClass.TOOL_UNAVAILABLE.value
    }
    compiled = any(
        command.stage == "compcert-compile" and command.succeeded
        for command in report.commands
    )
    unavailable = FailureClass.TOOL_UNAVAILABLE.value in report.failures
    if compiled and not meaningful_failures and not unavailable:
        report.status = "compatible"
    elif emission.succeeded and not meaningful_failures:
        report.status = "probe-incomplete"
    else:
        report.status = "incompatible"

    write_json(report, output / "report.json")
    write_markdown(report, output / "report.md")
    return report
