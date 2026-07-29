#!/usr/bin/env bash
# Per-certificate CompCert compile and native run timing for the
# certificates registered with `lean-compcert check-native`.
# Usage: bench/percert_native.sh [REPS]
set -u
REPS="${1:-5}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DIR="$ROOT/.lake/build/native-check"
OUT="$ROOT/bench/results"
mkdir -p "$OUT"
INC="-Iruntime/include -I$(lean --print-prefix)/include"

printf 'cert,bytes,compile_ms_median,run_ms_median,exe_bytes,exit\n' > "$OUT/percert_native.csv"

median() { python3 -c "
import sys
v=sorted(float(x) for x in sys.argv[1:])
n=len(v)
print('%.3f' % (v[n//2] if n%2 else (v[n//2-1]+v[n//2])/2))
" "$@"; }

cd "$ROOT"
for c in "$DIR"/*.c; do
  name="$(basename "$c" .c)"
  bytes=$(stat -c %s "$c")
  exe="$OUT/$name.bin"
  ctimes=()
  for _ in $(seq "$REPS"); do
    s=$(date +%s%N)
    ccomp $INC -o "$exe" "$c" > /dev/null 2>&1
    e=$(date +%s%N)
    ctimes+=( $(( (e-s)/1000 )) )   # microseconds
  done
  # convert us -> ms
  cmed_us=$(median "${ctimes[@]}")
  cmed=$(python3 -c "print('%.3f' % (${cmed_us}/1000.0))")
  rtimes=()
  ec=0
  for _ in $(seq "$REPS"); do
    s=$(date +%s%N)
    "$exe" > /dev/null 2>&1
    ec=$?
    e=$(date +%s%N)
    rtimes+=( $(( (e-s)/1000 )) )
  done
  rmed_us=$(median "${rtimes[@]}")
  rmed=$(python3 -c "print('%.3f' % (${rmed_us}/1000.0))")
  ebytes=$(stat -c %s "$exe" 2>/dev/null || echo 0)
  printf '%s,%s,%s,%s,%s,%s\n' "$name" "$bytes" "$cmed" "$rmed" "$ebytes" "$ec" >> "$OUT/percert_native.csv"
done
cat "$OUT/percert_native.csv"
