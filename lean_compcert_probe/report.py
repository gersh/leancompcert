from __future__ import annotations

import json
from pathlib import Path

from .model import ProbeReport


def write_json(report: ProbeReport, destination: Path) -> None:
    destination.write_text(
        json.dumps(report.as_dict(), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def write_markdown(report: ProbeReport, destination: Path) -> None:
    lines = [
        "# Lean–CompCert compatibility report",
        "",
        f"- Status: `{report.status}`",
        f"- Input: `{report.input}`",
        f"- Lean: `{report.lean_version or 'unknown'}`",
        f"- CompCert: `{report.compcert_version or 'unavailable'}`",
        f"- Target: `{report.compcert_target or 'unknown'}`",
        "",
        "## Stages",
        "",
        "| Stage | Exit | Time (ms) | Classification |",
        "|---|---:|---:|---|",
    ]
    for command in report.commands:
        classification = command.classification.value if command.classification else ""
        exit_code = "not run" if command.exit_code is None else str(command.exit_code)
        lines.append(
            f"| {command.stage} | {exit_code} | {command.duration_ms} | {classification} |"
        )
    if report.failures:
        lines.extend(["", "## Minimized failures", ""])
        for category, messages in report.failures.items():
            lines.append(f"### {category}")
            lines.append("")
            lines.extend(f"- `{message}`" for message in messages)
            lines.append("")
    if (
        report.compcert_compiled
        or report.conventionally_compiled
        or report.reference_artifacts
        or report.external_components
    ):
        lines.extend(["", "## Compilation boundary", ""])
        if report.compcert_compiled:
            lines.append("CompCert-compiled:")
            lines.append("")
            lines.extend(f"- `{item}`" for item in report.compcert_compiled)
            lines.append("")
        if report.conventionally_compiled:
            lines.append("Conventionally compiled for the final link:")
            lines.append("")
            lines.extend(f"- `{item}`" for item in report.conventionally_compiled)
            lines.append("")
        if report.reference_artifacts:
            lines.append("Reference-build-only sources:")
            lines.append("")
            lines.extend(f"- `{item}`" for item in report.reference_artifacts)
            lines.append("")
        if report.external_components:
            lines.append("External components:")
            lines.append("")
            lines.extend(f"- `{item}`" for item in report.external_components)
            lines.append("")
    if report.differential_match is not None:
        lines.extend(
            [
                "## Differential execution",
                "",
                "Outputs and exit codes "
                + ("matched." if report.differential_match else "did not match."),
                "",
            ]
        )
    destination.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
