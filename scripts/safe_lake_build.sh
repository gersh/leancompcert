#!/usr/bin/env bash
# Copyright (c) 2026 Gershon Bialer. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Run a LeanCompCert Lake build with a checkout lock, one worker by default,
# a hard cgroup memory ceiling, and no swap.  Production finite computations
# belong in emitted CompCert code; this cap catches accidental large kernel
# reductions and monolithic proof elaboration before they threaten the host.
set -euo pipefail

mem_high="${LCC_MEM_HIGH:-1300M}"
mem_max="${LCC_MEM_MAX:-1900M}"
swap_max="${LCC_SWAP_MAX:-0}"
jobs="${LCC_JOBS:-1}"
lock_file="${LCC_BUILD_LOCK:-$PWD/.lake/safe-build.lock}"

if [[ -n "${LCC_MEMORY_WRAPPER_ACTIVE:-}" ]]; then
  echo "error: nested LeanCompCert memory wrappers are not supported" >&2
  exit 75
fi
export LCC_MEMORY_WRAPPER_ACTIVE=1

if ! [[ "$jobs" =~ ^[1-9][0-9]*$ ]]; then
  echo "error: LCC_JOBS must be a positive integer" >&2
  exit 64
fi

mkdir -p "$(dirname "$lock_file")"
exec 9>"$lock_file"
if ! flock -n 9; then
  echo "error: another safe LeanCompCert build is running in this checkout" >&2
  exit 75
fi

export LEAN_NUM_THREADS="$jobs"
echo "safe_lake_build: jobs=$jobs MemoryHigh=$mem_high MemoryMax=$mem_max MemorySwapMax=$swap_max" >&2

if command -v systemd-run >/dev/null 2>&1; then
  exec systemd-run --user --scope --quiet \
    -p "MemoryAccounting=yes" \
    -p "MemoryHigh=$mem_high" \
    -p "MemoryMax=$mem_max" \
    -p "MemorySwapMax=$swap_max" \
    env "LEAN_NUM_THREADS=$LEAN_NUM_THREADS" lake build "$@"
fi

echo "warning: systemd-run unavailable; the build has no cgroup memory cap" >&2
exec lake build "$@"
