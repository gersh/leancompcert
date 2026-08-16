#!/usr/bin/env python3
"""Run all 120 proved RS62 configuration programs under no-swap caps."""

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
EMITTER = ROOT / "bench/RS62CheckpointConfigEmit.lean"
CERTIFICATE = ROOT / "LeanCompCert/Ports/RS62CheckpointConfigCertificate.lean"
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


def metric(metrics: Path, label: str) -> str:
    for line in metrics.read_text(encoding="utf-8").splitlines():
        if line.strip().startswith(label):
            return line.split(":", 1)[1].strip()
    raise ValueError(f"missing metric {label} in {metrics}")


def scoped_timed(
    command: list[str], metrics: Path, high: str, maximum: str
) -> tuple[float, str]:
    scoped = [
        "systemd-run", "--user", "--wait", "--collect", "--pipe", "--quiet",
        "-p", f"MemoryHigh={high}", "-p", f"MemoryMax={maximum}",
        "-p", "MemorySwapMax=0", f"--setenv=PATH={PATH_VALUE}",
        f"--working-directory={ROOT}", "/usr/bin/time", "-v", "-o",
        str(metrics), *command,
    ]
    start = time.monotonic()
    result = subprocess.run(
        scoped, cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    wall = time.monotonic() - start
    if result.returncode != 0:
        detail = metrics.read_text(encoding="utf-8") if metrics.exists() else ""
        raise SystemExit(
            f"command failed ({result.returncode}): {' '.join(command)}\n"
            f"{result.stdout}\n{detail}"
        )
    return wall, result.stdout


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output", type=Path,
        default=ROOT / "bench/results/manifests/rs62_checkpoint_config_120.json",
    )
    args = parser.parse_args()
    totals = {"emit": 0.0, "compile": 0.0, "run": 0.0}
    max_rss = {"emit": 0, "compile": 0, "run": 0}
    transcript: list[str] = []

    with tempfile.TemporaryDirectory(prefix="rs62-config-") as tmp_name:
        tmp = Path(tmp_name)
        for row in parse_rows():
            stem = f"r{row['idx']:03d}"
            c_file = tmp / f"{stem}.c"
            binary = tmp / stem
            metrics = {
                phase: tmp / f"{stem}.{phase}.time"
                for phase in ("emit", "compile", "run")
            }
            emit_cmd = [
                "/home/gersh/.elan/bin/lake", "env", "lean", "--run",
                str(EMITTER.relative_to(ROOT)), str(row["idx"]),
                str(row["rootCap"]), str(row["mainCount"]),
                str(row["segLen"]), str(row["markSteps"]), str(c_file),
            ]
            compile_cmd = [
                "/usr/local/bin/ccomp", "-O2", str(c_file), "-o", str(binary),
            ]
            run_cmd = [str(binary)]
            emit_wall, _ = scoped_timed(emit_cmd, metrics["emit"], "768M", "1G")
            compile_wall, _ = scoped_timed(
                compile_cmd, metrics["compile"], "768M", "1G"
            )
            run_wall, stdout = scoped_timed(run_cmd, metrics["run"], "128M", "256M")
            actual = stdout.strip().splitlines()
            expected = [f"count {row['mainCount']}", "budget 0"]
            if actual != expected:
                raise SystemExit(
                    f"{stem}: unexpected output\nexpected={expected}\nactual={actual}"
                )
            for phase, wall in (
                ("emit", emit_wall), ("compile", compile_wall), ("run", run_wall)
            ):
                totals[phase] += wall
                max_rss[phase] = max(
                    max_rss[phase],
                    int(metric(metrics[phase], "Maximum resident set size (kbytes)")),
                )
            transcript.append(f"{stem}:" + ";".join(actual))
            print(f"{stem} count={row['mainCount']} budget=0", flush=True)

    transcript_text = "\n".join(transcript) + "\n"
    result = {
        "schema": 1,
        "date": "2026-08-13",
        "status": "all 120 compiled configuration checks passed",
        "scope": "RS62 checkpoint rows 1..120",
        "checkpoint_count": 120,
        "sieve_bound": 134,
        "checked_outputs_per_checkpoint": ["exact_prime_count", "mark_budget_verdict"],
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
            str(CERTIFICATE.relative_to(ROOT)): sha256(CERTIFICATE),
        },
        "first_checkpoint": transcript[0],
        "last_checkpoint": transcript[-1],
        "trust_note": (
            "Prime enumeration and weighted summation ran only in CompCert-produced C. "
            "Lean proves the two array-program denotations and consumes their return words."
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
