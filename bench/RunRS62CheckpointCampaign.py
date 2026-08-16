#!/usr/bin/env python3
"""Run all RS62 checkpoint programs under fixed no-swap memory caps.

The Lean emitter only constructs verified programs from literal row metadata.
Prime marking, normalization, the no-wrap ladder check, the fail-safe audits,
and both endpoint folds execute in CompCert-produced binaries.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
ROWS_FILE = ROOT / "LeanCompCert/Ports/RS62CheckpointManifestData.lean"
EMITTER = ROOT / "bench/RS62SegmentedPipelineEmit.lean"
OVERFLOW_SOURCE = ROOT / "LeanCompCert/Ports/RS62PrimeMaskLadderOverflow.lean"
PATH_VALUE = "/home/gersh/.elan/bin:/usr/local/bin:/usr/bin:/bin"


ROW_RE = re.compile(
    r"\{ idx := (\d+), fuel := (\d+), lo := (\d+), segLen := (\d+), "
    r"rootCap := (\d+), mainCount := (\d+), markSteps := (\d+), "
    r"SL := (\d+), SU := (\d+), lower := (\d+), upper := (\d+) \}"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_rows() -> list[dict[str, int]]:
    names = [
        "idx", "fuel", "lo", "segLen", "rootCap", "mainCount",
        "markSteps", "SL", "SU", "lower", "upper",
    ]
    rows = [dict(zip(names, map(int, match))) for match in ROW_RE.findall(
        ROWS_FILE.read_text(encoding="utf-8")
    )]
    if len(rows) != 120:
        raise SystemExit(f"expected 120 manifest rows, found {len(rows)}")
    return rows


def timed(
    command: list[str], metrics: Path, cwd: Path, high: str, maximum: str
) -> tuple[float, str]:
    wrapped = [
        "systemd-run", "--user", "--wait", "--collect", "--pipe", "--quiet",
        "-p", f"MemoryHigh={high}", "-p", f"MemoryMax={maximum}",
        "-p", "MemorySwapMax=0", f"--setenv=PATH={PATH_VALUE}",
        f"--working-directory={cwd}", "/usr/bin/time", "-v", "-o",
        str(metrics), *command,
    ]
    start = time.monotonic()
    result = subprocess.run(
        wrapped, cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    wall = time.monotonic() - start
    if result.returncode != 0:
        raise SystemExit(
            f"command failed ({result.returncode}): {' '.join(command)}\n"
            f"{result.stdout}\n{metrics.read_text(encoding='utf-8')}"
        )
    return wall, result.stdout


def metric(metrics: Path, label: str) -> str:
    for line in metrics.read_text(encoding="utf-8").splitlines():
        if line.strip().startswith(label):
            return line.split(":", 1)[1].strip()
    raise ValueError(f"missing metric {label} in {metrics}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "bench/results/manifests/rs62_checkpoint_campaign_120.json",
    )
    args = parser.parse_args()
    rows = parse_rows()
    totals = {"emit": 0.0, "compile": 0.0, "run": 0.0}
    max_rss = {"emit": 0, "compile": 0, "run": 0}
    transcript: list[str] = []

    with tempfile.TemporaryDirectory(prefix="rs62-checkpoints-") as tmp_name:
        tmp = Path(tmp_name)
        for row in rows:
            stem = f"r{row['idx']:03d}"
            c_file = tmp / f"{stem}.c"
            binary = tmp / stem
            emit_metrics = tmp / f"{stem}.emit.time"
            compile_metrics = tmp / f"{stem}.compile.time"
            run_metrics = tmp / f"{stem}.run.time"
            scalar_args = [
                str(row[key]) for key in (
                    "lo", "segLen", "rootCap", "mainCount", "markSteps",
                    "SL", "SU", "lower", "upper",
                )
            ]
            emit_cmd = [
                "/home/gersh/.elan/bin/lake", "env", "lean", "--run",
                str(EMITTER.relative_to(ROOT)), *scalar_args, str(c_file),
            ]
            compile_cmd = [
                "/usr/local/bin/ccomp", "-O2", str(c_file),
                "-o", str(binary),
            ]
            run_cmd = [str(binary)]
            emit_wall, _ = timed(emit_cmd, emit_metrics, ROOT, "768M", "1G")
            compile_wall, _ = timed(
                compile_cmd, compile_metrics, ROOT, "768M", "1G"
            )
            run_wall, stdout = timed(
                run_cmd, run_metrics, ROOT, "128M", "256M"
            )
            expected = [
                "mark_audit 0", "mark 0", "norm 0", "overflow 0",
                "ladder_audit 0", f"lower {row['lower']}",
                f"upper {row['upper']}",
            ]
            actual = stdout.strip().splitlines()
            if actual != expected:
                raise SystemExit(
                    f"{stem}: unexpected output\nexpected={expected}\nactual={actual}"
                )
            for phase, wall, metrics in (
                ("emit", emit_wall, emit_metrics),
                ("compile", compile_wall, compile_metrics),
                ("run", run_wall, run_metrics),
            ):
                totals[phase] += wall
                max_rss[phase] = max(
                    max_rss[phase],
                    int(metric(metrics, "Maximum resident set size (kbytes)")),
                )
            transcript.append(f"{stem}:" + ";".join(actual))
            print(
                f"{stem} overflow=0 lower={row['lower']} upper={row['upper']}",
                flush=True,
            )

    transcript_text = "\n".join(transcript) + "\n"
    result = {
        "schema": 2,
        "date": "2026-08-13",
        "status": "all 120 compiled checkpoint and overflow checks passed",
        "scope": "RS62 checkpoint rows 1..120",
        "checkpoint_count": 120,
        "checked_outputs_per_checkpoint": [
            "mark_audit", "mark", "normalize", "ladder_overflow",
            "ladder_audit", "lower", "upper",
        ],
        "memory_limits": {
            "lean_emit": {"high": "768M", "max": "1G", "swap_max": "0"},
            "ccomp": {"high": "768M", "max": "1G", "swap_max": "0"},
            "run": {"high": "128M", "max": "256M", "swap_max": "0"},
        },
        "timings_seconds": {key: round(value, 3) for key, value in totals.items()},
        "max_rss_kb": max_rss,
        "aggregate_transcript": {
            "sha256": hashlib.sha256(transcript_text.encode()).hexdigest(),
            "format": "one canonical semicolon-separated line per checkpoint",
        },
        "source_artifacts": {
            str(ROWS_FILE.relative_to(ROOT)): sha256(ROWS_FILE),
            str(EMITTER.relative_to(ROOT)): sha256(EMITTER),
            str(OVERFLOW_SOURCE.relative_to(ROOT)): sha256(OVERFLOW_SOURCE),
        },
        "first_checkpoint": transcript[0],
        "last_checkpoint": transcript[-1],
        "trust_note": (
            "Every range-dependent loop ran in CompCert-produced code. "
            "The overflow stage checks the actual normalized prime mask; "
            "Lean does not evaluate the checkpoint folds."
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
