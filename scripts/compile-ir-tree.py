#!/usr/bin/env python3
"""Batch-compile a tree of Lean-generated C translation units with CompCert.

This is the whole-project companion to `lean-compcert-probe`: it walks a
`.lake/build/ir` tree (or any directory of Lean-emitted `.c` files), compiles
every translation unit to an object with `ccomp`, retries once with the
probe's mechanical ABI-preserving rewrites when the unchanged source is
rejected, and writes a machine-readable JSON report plus a console summary.

Objects and rewritten copies are placed in the output directory, never next
to the input sources. The rewrites applied are exactly
`lean_compcert_probe.rewrite.mechanical_rewrite`; nothing else is changed.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import shutil
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from lean_compcert_probe.rewrite import mechanical_rewrite


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("ir_root", type=Path, help="directory of generated .c files")
    parser.add_argument("--ccomp", default="ccomp", help="CompCert compiler path")
    parser.add_argument(
        "--include",
        action="append",
        default=[],
        help="include directory (repeatable, searched in order)",
    )
    parser.add_argument("--jobs", type=int, default=4, help="parallel compilations")
    parser.add_argument(
        "--output", type=Path, required=True, help="output directory for objects and report"
    )
    parser.add_argument(
        "--report", type=Path, default=None, help="report path (default OUTPUT/report.json)"
    )
    parser.add_argument(
        "--keep-going",
        action="store_true",
        help="continue after failures (always on; retained for compatibility)",
    )
    return parser.parse_args()


def ccomp_version(ccomp: str) -> str:
    result = subprocess.run(
        [ccomp, "-version"], capture_output=True, text=True, check=False
    )
    return (result.stdout or result.stderr).strip().splitlines()[0]


def compile_unit(
    source: Path,
    ir_root: Path,
    output: Path,
    ccomp: str,
    includes: list[str],
) -> dict:
    relative = source.relative_to(ir_root)
    object_path = output / "objects" / relative.with_suffix(".o")
    object_path.parent.mkdir(parents=True, exist_ok=True)
    command = [ccomp, *[f"-I{path}" for path in includes], "-c", "-o", str(object_path)]
    started = time.monotonic()

    direct = subprocess.run(
        [*command, str(source)], capture_output=True, text=True, check=False
    )
    if direct.returncode == 0:
        return {
            "unit": str(relative),
            "status": "compiled",
            "rewrites": [],
            "seconds": round(time.monotonic() - started, 3),
        }

    rewritten = mechanical_rewrite(source.read_text())
    if rewritten.applied:
        rewritten_path = output / "rewritten" / relative.with_suffix(".rewritten.c")
        rewritten_path.parent.mkdir(parents=True, exist_ok=True)
        rewritten_path.write_text(rewritten.text)
        retried = subprocess.run(
            [*command, str(rewritten_path)], capture_output=True, text=True, check=False
        )
        if retried.returncode == 0:
            return {
                "unit": str(relative),
                "status": "compiled-after-rewrite",
                "rewrites": list(rewritten.applied),
                "seconds": round(time.monotonic() - started, 3),
            }
        stderr = retried.stderr
    else:
        stderr = direct.stderr

    return {
        "unit": str(relative),
        "status": "rejected",
        "rewrites": list(rewritten.applied),
        "diagnostics": stderr.strip().splitlines()[:8],
        "seconds": round(time.monotonic() - started, 3),
    }


def main() -> int:
    args = parse_args()
    ir_root = args.ir_root.resolve()
    sources = sorted(ir_root.rglob("*.c"))
    if not sources:
        print(f"error: no .c files under {ir_root}", file=sys.stderr)
        return 2
    if shutil.which(args.ccomp) is None:
        print(f"error: {args.ccomp} not found", file=sys.stderr)
        return 2

    args.output.mkdir(parents=True, exist_ok=True)
    report_path = args.report or (args.output / "report.json")

    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [
            pool.submit(
                compile_unit, source, ir_root, args.output, args.ccomp, args.include
            )
            for source in sources
        ]
        for index, future in enumerate(concurrent.futures.as_completed(futures), 1):
            result = future.result()
            results.append(result)
            if result["status"] == "rejected" or index % 100 == 0:
                print(f"[{index}/{len(sources)}] {result['status']}: {result['unit']}")

    results.sort(key=lambda entry: entry["unit"])
    summary = {
        "irRoot": str(ir_root),
        "ccomp": ccomp_version(args.ccomp),
        "includes": args.include,
        "units": len(results),
        "compiled": sum(r["status"] == "compiled" for r in results),
        "compiledAfterRewrite": sum(
            r["status"] == "compiled-after-rewrite" for r in results
        ),
        "rejected": sum(r["status"] == "rejected" for r in results),
        "results": results,
    }
    report_path.write_text(json.dumps(summary, indent=2) + "\n")

    print(
        f"\n{summary['units']} units: {summary['compiled']} compiled, "
        f"{summary['compiledAfterRewrite']} after mechanical rewrite, "
        f"{summary['rejected']} rejected"
    )
    print(f"report: {report_path}")
    return 0 if summary["rejected"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
