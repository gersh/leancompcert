#!/usr/bin/env bash
# Cost of the A.36 low-branch interval-bisection sweep as an artifact.
#
#   bench/a36_bisect.sh DEPTH [DEPTH ...]
#
# One artifact per depth: emit rolled C, compile it freestanding with CompCert,
# run it, and record the size and the wall time.  Exit status 0 means every leaf
# passed (`l_A36Bisect<d>() == 0`); 1 means at least one leaf failed its root
# check or its residual comparison; anything else is abnormal termination and is
# NOT a mathematical disagreement.
#
# DEPTH 8 is the depth the source certificate uses and the one
# `LeanCompCert.Ports.A36Bisect.sweep_ok` proves in Lean's kernel.  Deeper runs
# are cost measurements; a finer grid is a strictly stronger enclosure, but no
# Lean theorem is attached to it until the body/`leafOK` simulation is proved.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/bench/results"
mkdir -p "$OUT"
. "$ROOT/bench/freestanding.sh"
fs_init "$ROOT" || exit 1
cd "$ROOT"

CSV="$OUT/a36_bisect.csv"
printf 'depth,leaves,body_instrs,c_bytes,exe_bytes,ccomp_ms,run_s,ns_per_leaf,exit\n' > "$CSV"

for d in "$@"; do
  c="$OUT/a36_bisect_$d.c"
  info=$(lake env lean --run bench/A36BisectEmit.lean "$d" "$c") || { echo "emit failed $d"; continue; }
  body=$(echo "$info" | sed 's/.*body = \([0-9]*\).*/\1/')
  leaves=$(echo "$info" | sed 's/.*leaves = \([0-9]*\),.*/\1/')
  cb=$(stat -c %s "$c")
  exe="$OUT/a36_bisect_$d.bin"
  s=$(date +%s%N); fs_cc "$exe" "$c" || { echo "ccomp failed $d"; continue; }; e=$(date +%s%N)
  cm=$(python3 -c "print('%.1f' % ((${e}-${s})/1e6))")
  eb=$(stat -c %s "$exe")
  s=$(date +%s%N); "$exe"; ec=$?; e=$(date +%s%N)
  rs=$(python3 -c "print('%.4f' % ((${e}-${s})/1e9))")
  npl=$(python3 -c "print('%.1f' % ((${e}-${s})/$leaves))")
  printf '%s,%s,%s,%s,%s,%s,%s,%s,%s\n' \
    "$d" "$leaves" "$body" "$cb" "$eb" "$cm" "$rs" "$npl" "$ec" >> "$CSV"
  echo "depth=$d leaves=$leaves body=$body c=${cb}B exe=${eb}B ccomp=${cm}ms run=${rs}s ${npl}ns/leaf exit=$ec"
done
