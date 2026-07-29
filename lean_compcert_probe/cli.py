from __future__ import annotations

import argparse
import sys
from pathlib import Path

from .probe import run_probe


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        prog="lean-compcert-probe",
        description="Probe Lean-generated C for CompCert compatibility.",
    )
    result.add_argument("input", type=Path, help="Lean source file")
    result.add_argument(
        "--output",
        type=Path,
        help="report directory (default: .lake/build/lean-compcert-probe/<module>)",
    )
    result.add_argument("--lean", default="lean", help="Lean executable")
    result.add_argument("--ccomp", default="ccomp", help="CompCert ccomp executable")
    result.add_argument("--target", help="CompCert target")
    result.add_argument("--timeout", type=float, default=120, help="per-command timeout")
    result.add_argument(
        "--opt-level", choices=("0", "1", "2"), default="1", help="CompCert optimization level"
    )
    result.add_argument(
        "--debug-symbols", action="store_true", help="request debug information from CompCert"
    )
    result.add_argument(
        "--attempt-rewrites",
        action="store_true",
        help="probe a separate copy with conservative mechanical rewrites",
    )
    result.add_argument(
        "--differential-check",
        action="store_true",
        help="build and compare conventional and CompCert native executables",
    )
    result.add_argument(
        "--run-arg",
        action="append",
        default=[],
        help="argument passed to both executables (repeatable)",
    )
    result.add_argument(
        "--reference-command",
        help="ordinary Lean executable command for differential execution",
    )
    result.add_argument(
        "--candidate-command",
        help="CompCert executable command for differential execution",
    )
    return result


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    if not args.input.is_file():
        print(f"error: input does not exist: {args.input}", file=sys.stderr)
        return 2
    output = args.output or (
        Path(".lake") / "build" / "lean-compcert-probe" / args.input.stem
    )
    report = run_probe(
        source=args.input,
        output=output,
        lean=args.lean,
        ccomp=args.ccomp,
        target=args.target,
        timeout=args.timeout,
        attempt_rewrites=args.attempt_rewrites,
        debug_symbols=args.debug_symbols,
        opt_level=args.opt_level,
        differential_check=args.differential_check,
        run_args=tuple(args.run_arg),
        reference_command=args.reference_command,
        candidate_command=args.candidate_command,
    )
    print(f"{report.status}: {output / 'report.md'}")
    # Exit codes: 0 compatible, 1 incompatible, 2 usage error, 3 incomplete
    # (a required tool was unavailable, so nothing was actually verified).
    if report.status == "compatible":
        return 0
    if report.status == "probe-incomplete":
        return 3
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
