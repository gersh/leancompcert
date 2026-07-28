from __future__ import annotations

import json
import platform
import shutil
from pathlib import Path

from lean_compcert_probe.classify import classify_failure, minimize_diagnostics
from lean_compcert_probe.process import run_command


def check_runtime(
    root: Path,
    output: Path,
    ccomp: str,
    target: str | None,
    timeout: float,
) -> tuple[bool, dict[str, object]]:
    output.mkdir(parents=True, exist_ok=True)
    compiler = shutil.which(ccomp)
    if compiler is None and Path(ccomp).is_file():
        compiler = str(Path(ccomp).resolve())
    if compiler is None:
        payload: dict[str, object] = {
            "status": "tool-unavailable",
            "compiler": ccomp,
            "files": [],
        }
        (output / "runtime-compatibility.json").write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        return False, payload

    prefix = run_command("lean-prefix", ["lean", "--print-prefix"], root, timeout)
    version = run_command(
        "compcert-version", [compiler, "-version"], root, timeout
    )
    lean_include = (
        Path(prefix.stdout.strip()) / "include" if prefix.succeeded else None
    )
    target_args = ["-target", target] if target else []
    entries: list[dict[str, object]] = []
    compatible = True
    for source in sorted((root / "runtime").glob("**/*.c")):
        relative = source.relative_to(root).as_posix()
        object_file = output / (relative.replace("/", "_") + ".o")
        expected_adapter = relative.startswith("runtime/adapters/")
        include_args: list[str] = []
        if not expected_adapter:
            include_args = ["-I", str(root / "runtime" / "include")]
            if lean_include is not None:
                include_args += ["-I", str(lean_include)]
        result = run_command(
            "runtime-compile",
            [
                compiler,
                *target_args,
                *include_args,
                "-c",
                str(source),
                "-o",
                str(object_file),
            ],
            root,
            timeout,
        )
        if result.succeeded:
            status = "COMPATIBLE"
        elif expected_adapter:
            status = "ADAPTED"
        else:
            status = "UNSUPPORTED"
            compatible = False
        entry: dict[str, object] = {
            "source": relative,
            "status": status,
            "exitCode": result.exit_code,
            "command": result.command,
        }
        if not result.succeeded:
            entry["classification"] = classify_failure(
                result.stderr, "compcert-compile"
            ).value
            entry["diagnostics"] = minimize_diagnostics(result.stderr)
        entries.append(entry)
    payload = {
        "status": "compatible" if compatible else "incompatible",
        "compiler": compiler,
        "compilerVersion": (
            (version.stdout or version.stderr).strip().splitlines()[0]
            if version.succeeded and (version.stdout or version.stderr).strip()
            else None
        ),
        "target": target or (
            f"{platform.machine() or 'unknown'}-"
            f"{platform.system().lower() or 'unknown'}"
        ),
        "targetSelection": "explicit" if target else "ccomp-default-host-inferred",
        "versionCommand": version.command,
        "files": entries,
    }
    (output / "runtime-compatibility.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return compatible, payload
