#!/usr/bin/env python3
"""Run the root-only LeanCompCert receipts for the Platt (2.11) manifest.

This is deliberately separate from the 10^12-element residue campaign.  For
each retained row it emits the exact formal ``rootOnlyProgram`` and its
fail-safe audit, compiles both with CompCert, and checks the returned write
cursor/audit word.  The JSONL receipt is resumable and belongs under ``runs``;
only the compact completed summary is intended for version control.
"""

from __future__ import annotations

import argparse
import bisect
import concurrent.futures
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "bench/results/manifests/platt211_1e12.json"
MANIFEST_SHA256 = "3ed737cb9ad2dd5a107d46c08d179e351850c199482ec487443c35d998f4cb3e"
EMITTER = ROOT / "bench/Platt211RootBatch.lean"
VALUE_RE = re.compile(r"^(write_cursor|audit) (\d+)$", re.MULTILINE)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def primes_through(limit: int) -> list[int]:
    mark = bytearray(b"\x01") * (limit + 1)
    mark[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if mark[p]:
            mark[p * p:limit + 1:p] = b"\x00" * (
                (limit - p * p) // p + 1
            )
    return [n for n in range(2, limit + 1) if mark[n]]


def load_rows(limit: int | None) -> list[dict]:
    if sha256(MANIFEST) != MANIFEST_SHA256:
        raise RuntimeError("pinned production manifest hash changed")
    doc = json.loads(MANIFEST.read_text())
    rows = doc.get("windows")
    if len(rows) != 1092 or doc.get("range") != [1, 10**12]:
        raise RuntimeError("not the complete pinned Platt manifest")
    primes = primes_through(10**6)
    jobs = []
    for idx, row in enumerate(rows):
        if row["idx"] != idx:
            raise RuntimeError(f"manifest index mismatch at {idx}")
        root_cap = math.isqrt(row["hi"])
        root_count = max(1, (root_cap + row["seglen"] - 1) // row["seglen"])
        boot_bound = max(math.isqrt(root_count * row["seglen"]), 2)
        main_count = bisect.bisect_right(primes, max(boot_bound, root_cap))
        # The formal certificate adds one inert, root-cap-gated cell when a
        # one-window root interval ends exactly on the segment boundary.
        # Its table cursor is consequently based after that padded segment.
        certificate_seglen = (
            row["seglen"] + 1
            if root_count == 1 and root_cap == row["seglen"]
            else row["seglen"]
        )
        expected = 3 * certificate_seglen + 1 + main_count
        jobs.append({
            "idx": idx,
            "root_cap": root_cap,
            "seglen": row["seglen"],
            "certificate_seglen": certificate_seglen,
            "expected": expected,
        })
    return jobs if limit is None else jobs[:limit]


def paths(outdir: Path, idx: int, mode: str) -> tuple[Path, Path]:
    stem = outdir / f"row-{idx:04d}-{mode}"
    return stem.with_suffix(".c"), stem.with_suffix(".x")


def emit(jobs: list[dict], outdir: Path) -> float:
    pending = []
    for job in jobs:
        for mode in ("root", "audit"):
            c_path, _ = paths(outdir, job["idx"], mode)
            if not c_path.exists():
                pending.append((job, mode, c_path))
    if not pending:
        return 0.0
    jobfile = outdir / "emit-jobs.txt"
    jobfile.write_text("".join(
        f"{job['idx']} {mode} {c_path}\n"
        for job, mode, c_path in pending
    ))
    env = dict(os.environ, LEAN_PATH=str(ROOT / ".lake/build/lib/lean"))
    t0 = time.time()
    result = subprocess.run(
        ["lake", "env", "lean", "--run", str(EMITTER), str(jobfile)],
        cwd=ROOT, env=env, capture_output=True, text=True,
    )
    if result.returncode:
        raise RuntimeError(f"batch emitter failed:\n{result.stderr[-6000:]}")
    return time.time() - t0


def compile_one(item: tuple[dict, str], outdir: Path, ccomp: str) -> None:
    job, mode = item
    c_path, x_path = paths(outdir, job["idx"], mode)
    if x_path.exists():
        return
    result = subprocess.run(
        [ccomp, "-O2", "-o", str(x_path), str(c_path)],
        capture_output=True, text=True,
    )
    if result.returncode:
        raise RuntimeError(
            f"CompCert failed for row {job['idx']} {mode}:\n"
            f"{result.stderr[-4000:]}"
        )


def run_one(item: tuple[dict, str], outdir: Path) -> dict:
    job, mode = item
    _, x_path = paths(outdir, job["idx"], mode)
    t0 = time.time()
    result = subprocess.run([str(x_path)], capture_output=True, text=True)
    elapsed = time.time() - t0
    match = VALUE_RE.search(result.stdout)
    if result.returncode or not match:
        raise RuntimeError(
            f"run failed for row {job['idx']} {mode}, rc={result.returncode}:\n"
            f"{result.stdout[-1000:]}\n{result.stderr[-1000:]}"
        )
    label, value_s = match.groups()
    value = int(value_s)
    expected = 0 if mode == "audit" else job["expected"]
    expected_label = "audit" if mode == "audit" else "write_cursor"
    if label != expected_label or value != expected:
        raise RuntimeError(
            f"row {job['idx']} {mode}: got {label}={value}, expected "
            f"{expected_label}={expected}"
        )
    return {
        "idx": job["idx"], "mode": mode, "root_cap": job["root_cap"],
        "seglen": job["seglen"],
        "certificate_seglen": job["certificate_seglen"],
        "expected": expected,
        "seconds": round(elapsed, 6),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--outdir", type=Path, default=ROOT / "runs/platt211_root")
    parser.add_argument("--summary", type=Path,
                        default=ROOT / "bench/results/platt211_root_1e12.json")
    parser.add_argument("--workers", type=int, default=12)
    parser.add_argument("--compile-workers", type=int, default=4)
    parser.add_argument("--limit", type=int)
    args = parser.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    jobs = load_rows(args.limit)
    receipt = args.outdir / "receipt.jsonl"
    done: dict[tuple[int, str], dict] = {}
    if receipt.exists():
        for line in receipt.read_text().splitlines():
            row = json.loads(line)
            done[(row["idx"], row["mode"])] = row
    items = [(job, mode) for job in jobs for mode in ("root", "audit")
             if (job["idx"], mode) not in done]

    emit_seconds = emit([job for job in jobs
                         if any((job["idx"], m) not in done
                                for m in ("root", "audit"))], args.outdir)
    ccomp = shutil.which("ccomp")
    if not ccomp:
        raise RuntimeError("ccomp is not on PATH")
    t_compile = time.time()
    with concurrent.futures.ThreadPoolExecutor(
            max_workers=max(1, args.compile_workers)) as pool:
        list(pool.map(lambda item: compile_one(item, args.outdir, ccomp), items))
    compile_seconds = time.time() - t_compile

    t_run = time.time()
    with receipt.open("a", buffering=1) as out:
        with concurrent.futures.ThreadPoolExecutor(
                max_workers=max(1, args.workers)) as pool:
            for result in pool.map(lambda item: run_one(item, args.outdir), items):
                out.write(json.dumps(result, sort_keys=True) + "\n")
                done[(result["idx"], result["mode"])] = result
    run_seconds = time.time() - t_run

    for job, mode in items:
        c_path, x_path = paths(args.outdir, job["idx"], mode)
        c_path.unlink(missing_ok=True)
        x_path.unlink(missing_ok=True)

    complete = len(done) == 2 * len(jobs)
    summary = {
        "certificate": "Platt (2.11) root-only prime-table cursor and audit",
        "manifest_sha256": MANIFEST_SHA256,
        "rows": len(jobs),
        "receipts": len(done),
        "complete": complete,
        "compcert": subprocess.run([ccomp, "-version"], capture_output=True,
                                     text=True).stdout.strip(),
        "workers": args.workers,
        "compile_workers": args.compile_workers,
        "latest_emit_seconds": round(emit_seconds, 3),
        "latest_compile_seconds": round(compile_seconds, 3),
        "latest_run_seconds": round(run_seconds, 3),
        "receipt_sha256": sha256(receipt),
    }
    if args.limit is None and complete:
        args.summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
