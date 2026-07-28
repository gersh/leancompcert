from __future__ import annotations

import hashlib
import json
import struct
import subprocess
import sys
from pathlib import Path

from lean_compcert_probe.model import ProbeReport

from . import __version__


def _git_revision(root: Path) -> str | None:
    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return completed.stdout.strip() if completed.returncode == 0 else None


def runtime_hash(root: Path) -> str:
    digest = hashlib.sha256()
    inputs = [
        ("project/runtime/include/stdatomic.h", root / "runtime" / "include" / "stdatomic.h"),
        ("project/runtime/adapters/atomics.c", root / "runtime" / "adapters" / "atomics.c"),
        ("project/runtime/portable/unreachable.c", root / "runtime" / "portable" / "unreachable.c"),
        ("project/runtime/inventory.yaml", root / "runtime" / "inventory.yaml"),
    ]
    prefix = subprocess.run(
        ["lean", "--print-prefix"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    if prefix.returncode == 0:
        include = Path(prefix.stdout.strip()) / "include" / "lean"
        inputs.extend(
            (f"lean/{name}", include / name)
            for name in ("config.h", "lean.h", "version.h")
        )
    for label, path in inputs:
        digest.update(label.encode())
        digest.update(b"\0")
        digest.update(path.read_bytes() if path.is_file() else b"<missing>")
        digest.update(b"\0")
    return digest.hexdigest()


def abi_manifest(root: Path, lean_version: str | None) -> dict[str, object]:
    return {
        "schemaVersion": 1,
        "leanVersion": lean_version,
        "pointerBits": struct.calcsize("P") * 8,
        "endianness": sys.byteorder,
        "objectAlignment": struct.calcsize("P"),
        "scalarTagBits": 1,
        "closureLayoutVersion": 1,
        "runtimeAbiHash": runtime_hash(root),
    }


def write_build_manifest(
    root: Path,
    report: ProbeReport,
    destination: Path,
    profile: str,
    runtime_mode: str,
) -> dict[str, object]:
    destination.parent.mkdir(parents=True, exist_ok=True)
    abi = abi_manifest(root, report.lean_version)
    abi_path = destination.parent / "abi-manifest.json"
    abi_path.write_text(
        json.dumps(abi, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    payload: dict[str, object] = {
        "schemaVersion": 1,
        "leanVersion": report.lean_version,
        "leanGitRevision": report.lean_git_revision,
        "backendVersion": __version__,
        "backendGitRevision": _git_revision(root),
        "compcertVersion": report.compcert_version,
        "compcertTarget": report.compcert_target,
        "runtimeMode": runtime_mode,
        "runtimeAbiHash": abi["runtimeAbiHash"],
        "abiManifest": str(abi_path),
        "runtimeAbi": abi,
        "profile": profile,
        "pipeline": "normalized-lean-c",
        "assuranceBoundary": (
            "CompCert C-to-assembly semantic preservation for accepted application "
            "modules; Lean frontend, normalization, runtime, assembler, linker, and "
            "external functions remain trusted."
        ),
        "modules": [
            {
                "input": report.input,
                "generatedC": report.generated_c,
                "rewrittenC": report.rewritten_c,
                "compCertCompiled": report.compcert_compiled,
            }
        ],
        "externalObjects": report.conventionally_compiled,
        "referenceArtifacts": report.reference_artifacts,
        "systemLibraries": report.external_components,
        "unsupportedFeatures": [
            {"category": category, "messages": messages}
            for category, messages in report.failures.items()
        ],
        "compilerCommands": [
            {
                "stage": result.stage,
                "command": result.command,
                "exitCode": result.exit_code,
            }
            for result in report.commands
        ],
        "differentialMatch": report.differential_match,
        "status": report.status,
    }
    destination.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return payload
