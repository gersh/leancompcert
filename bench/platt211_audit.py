#!/usr/bin/env python3
"""Run fail-safe LeanCompCert audits for the retained Platt (2.11) chain.

The original two-phase campaign recorded exact configurations, carry seeds,
and output cells for 1,092 CompCert-compiled windows.  A compiled result does
not by itself prove that the partial array source was defined.  This runner
re-emits ``auditProgram (mobiusProgram ...)`` for those exact manifest rows,
compiles every transform with CompCert, and requires every sticky audit result
to be zero.

The JSONL receipt is resumable.  A row is reused only when all configuration
and seed fields still match the immutable production manifest.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_MANIFEST = ROOT / "bench/results/manifests/platt211_1e12.json"
DEFAULT_MANIFEST_SHA256 = (
    "3ed737cb9ad2dd5a107d46c08d179e351850c199482ec487443c35d998f4cb3e"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def load_jobs(manifest_path: Path) -> tuple[dict, list[dict]]:
    manifest = json.loads(manifest_path.read_text())
    if manifest_path.resolve() == DEFAULT_MANIFEST.resolve():
        actual = sha256(manifest_path)
        if actual != DEFAULT_MANIFEST_SHA256:
            raise RuntimeError(
                f"production manifest hash changed: {actual} != "
                f"{DEFAULT_MANIFEST_SHA256}"
            )
    if manifest.get("range") != [1, 10**12]:
        raise RuntimeError("manifest is not the exact [1, 10^12] campaign")
    rows = manifest.get("windows")
    if not isinstance(rows, list) or len(rows) != 1092:
        raise RuntimeError("manifest does not contain exactly 1,092 windows")
    if manifest.get("failures") != [] or not manifest.get(
        "phaseB_covers_all_windows"
    ):
        raise RuntimeError("refusing a rejected or partial production manifest")

    jobs = []
    previous_hi = 0
    previous_out = None
    for expected_idx, row in enumerate(rows):
        required = ("idx", "lo", "hi", "seglen", "segcount", "seed", "slots")
        if any(key not in row for key in required):
            raise RuntimeError(f"manifest row {expected_idx} is incomplete")
        if row["idx"] != expected_idx or row["lo"] != previous_hi + 1:
            raise RuntimeError(f"manifest chain breaks at row {expected_idx}")
        if row["hi"] != row["lo"] + row["seglen"] * row["segcount"] - 1:
            raise RuntimeError(f"manifest sizing is inconsistent at row {expected_idx}")
        if previous_out is not None and row["seed"] != previous_out:
            raise RuntimeError(f"manifest carry breaks at row {expected_idx}")
        if len(row["slots"]) < 3:
            raise RuntimeError(f"manifest observation is incomplete at row {expected_idx}")
        jobs.append(
            {
                "idx": row["idx"],
                "lo": row["lo"],
                "hi": row["hi"],
                "seglen": row["seglen"],
                "segcount": row["segcount"],
                "seed": row["seed"],
            }
        )
        previous_hi = row["hi"]
        previous_out = row["slots"][0]
    if previous_hi != 10**12:
        raise RuntimeError("manifest does not end at 10^12")
    return manifest, jobs


def receipt_matches(receipt: dict, job: dict) -> bool:
    return all(receipt.get(key) == job[key] for key in (
        "idx", "lo", "hi", "seglen", "segcount", "seed"
    )) and receipt.get("audit_return") == 0


def emit_batches(jobs: list[dict], work: Path, batches: int) -> float:
    ordered = sorted(jobs, key=lambda job: -(job["hi"] - job["lo"] + 1))
    chunks = [ordered[index::batches] for index in range(batches)]
    job_files = []
    for index, chunk in enumerate(chunks):
        if not chunk:
            continue
        path = work / f"emit_{index}.jobs"
        with path.open("w") as handle:
            for job in chunk:
                output = work / f"w{job['idx']:06d}.c"
                handle.write(
                    f"{job['idx']} platt211audit {job['lo']} "
                    f"{job['seglen']} {job['segcount']} {output} "
                    f"{job['seed']}\n"
                )
        job_files.append(path)

    def emit(path: Path) -> None:
        result = subprocess.run(
            ["lake", "env", "lean", "--run", "bench/ArraySegBatch.lean", str(path)],
            cwd=ROOT,
            text=True,
            capture_output=True,
        )
        if result.returncode != 0:
            raise RuntimeError(
                f"audit emission failed for {path}:\n{result.stderr[-4000:]}"
            )

    started = time.monotonic()
    with ThreadPoolExecutor(max_workers=max(1, len(job_files))) as executor:
        list(executor.map(emit, job_files))
    return time.monotonic() - started


def compile_all(jobs: list[dict], work: Path, streams: int, cc: str) -> float:
    chunks = [jobs[index::streams] for index in range(streams)]

    def compile_chunk(chunk: list[dict]) -> None:
        for job in chunk:
            base = work / f"w{job['idx']:06d}"
            result = subprocess.run(
                [cc, "-O2", "-o", str(base.with_suffix(".x")), str(base.with_suffix(".c"))],
                text=True,
                capture_output=True,
            )
            if result.returncode != 0:
                raise RuntimeError(
                    f"CompCert failed at window {job['idx']}:\n{result.stderr[-4000:]}"
                )

    started = time.monotonic()
    with ThreadPoolExecutor(max_workers=streams) as executor:
        list(executor.map(compile_chunk, [chunk for chunk in chunks if chunk]))
    return time.monotonic() - started


def run_all(
    jobs: list[dict], work: Path, receipt_path: Path, workers: int
) -> tuple[float, float]:
    lock = threading.Lock()
    completed = 0
    core_seconds = 0.0
    started = time.monotonic()
    receipt_file = receipt_path.open("a")

    def run(job: dict) -> None:
        nonlocal completed, core_seconds
        executable = work / f"w{job['idx']:06d}.x"
        before = time.monotonic()
        result = subprocess.run([str(executable)])
        elapsed = time.monotonic() - before
        if result.returncode != 0:
            raise RuntimeError(
                f"audit rejected window {job['idx']} [{job['lo']}, {job['hi']}], "
                f"exit {result.returncode}"
            )
        receipt = dict(job, audit_return=0, elapsed_seconds=round(elapsed, 6))
        with lock:
            receipt_file.write(json.dumps(receipt, sort_keys=True) + "\n")
            receipt_file.flush()
            completed += 1
            core_seconds += elapsed
            if completed % 25 == 0 or completed == len(jobs):
                print(
                    f"audit {completed}/{len(jobs)}: window {job['idx']} "
                    f"[{job['lo']}, {job['hi']}] {elapsed:.2f}s",
                    flush=True,
                )
        executable.unlink()
        (work / f"w{job['idx']:06d}.c").unlink()

    try:
        with ThreadPoolExecutor(max_workers=workers) as executor:
            list(executor.map(run, jobs))
    finally:
        receipt_file.close()
    return time.monotonic() - started, core_seconds


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--outdir", type=Path, default=ROOT / "runs/platt211_audit")
    parser.add_argument("--workers", type=int, default=12)
    parser.add_argument("--streams", type=int, default=3)
    parser.add_argument("--batches", type=int, default=4)
    parser.add_argument("--cc", default="ccomp")
    parser.add_argument("--limit", type=int, default=0,
                        help="run only the first N pending windows (smoke/resume)")
    parser.add_argument("--unsafe-control", action="store_true",
                        help="run one lo=0 division-by-zero rejection control")
    args = parser.parse_args()
    if min(args.workers, args.streams, args.batches) < 1:
        parser.error("workers, streams, and batches must be positive")

    args.outdir.mkdir(parents=True, exist_ok=True)
    work = args.outdir / "work"
    work.mkdir(exist_ok=True)
    if args.unsafe_control:
        control = {
            "idx": 0,
            "lo": 0,
            "hi": 0,
            "seglen": 1,
            "segcount": 1,
            "seed": 1 << 63,
        }
        emit_wall = emit_batches([control], work, 1)
        compile_wall = compile_all([control], work, 1, args.cc)
        result = subprocess.run([str(work / "w000000.x")])
        print(
            f"unsafe control: exit={result.returncode}, emission={emit_wall:.3f}s, "
            f"CompCert={compile_wall:.3f}s",
            flush=True,
        )
        return 0 if result.returncode == 1 else 1

    manifest, jobs = load_jobs(args.manifest)
    receipt_path = args.outdir / "audit.jsonl"
    done = {}
    if receipt_path.exists():
        for line in receipt_path.read_text().splitlines():
            if line.strip():
                row = json.loads(line)
                done[row["idx"]] = row
    for job in jobs:
        if job["idx"] in done and not receipt_matches(done[job["idx"]], job):
            raise RuntimeError(f"stale audit receipt for window {job['idx']}")
    pending = [job for job in jobs if job["idx"] not in done]
    if args.limit:
        pending = pending[: args.limit]
    print(
        f"production manifest {sha256(args.manifest)}: {len(jobs)} windows, "
        f"{len(done)} completed, {len(pending)} selected",
        flush=True,
    )
    if not pending:
        return 0

    emit_wall = emit_batches(pending, work, args.batches)
    print(f"emission: {emit_wall:.2f}s", flush=True)
    compile_wall = compile_all(pending, work, args.streams, args.cc)
    print(f"CompCert compilation: {compile_wall:.2f}s", flush=True)
    run_wall, core_seconds = run_all(pending, work, receipt_path, args.workers)
    summary = {
        "manifest_sha256": sha256(args.manifest),
        "manifest_windows": len(manifest["windows"]),
        "selected_windows": len(pending),
        "emission_wall_seconds": round(emit_wall, 3),
        "compilation_wall_seconds": round(compile_wall, 3),
        "run_wall_seconds": round(run_wall, 3),
        "run_core_seconds": round(core_seconds, 3),
    }
    print(json.dumps(summary, sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
