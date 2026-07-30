#!/usr/bin/env bash
# CompCert compile time + native run time for rolled emission as a function of
# loop count.  Usage: bench/rolled_compcert.sh N:VALUE [N:VALUE ...]
# VALUE is the certified constant (precomputed so that emission cost is
# measured without the interpreter's evaluation of `Program.denote`).
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/bench/results"
mkdir -p "$OUT"
. "$ROOT/bench/freestanding.sh"
fs_init "$ROOT" || exit 1
trap fs_cleanup EXIT
REPS=5
cd "$ROOT"

median() { python3 -c "
import sys
v=sorted(float(x) for x in sys.argv[1:]); n=len(v)
print('%.3f' % (v[n//2] if n%2 else (v[n//2-1]+v[n//2])/2))" "$@"; }

printf 'loop_count,c_bytes,exe_bytes,emit_s,compcert_compile_ms,native_run_ms,exit\n' \
  > "$OUT/rolled_compcert.csv"

for spec in "$@"; do
  n="${spec%%:*}"; v="${spec##*:}"
  c="$OUT/rolled_$n.c"
  es=$(date +%s%N)
  lake env lean --run bench/RolledEmit.lean "$n" "$c" "$v" > /dev/null || { echo "emit failed $n"; continue; }
  ee=$(date +%s%N)
  emit=$(python3 -c "print('%.3f' % ((${ee}-${es})/1e9))")
  cb=$(stat -c %s "$c")
  exe="$OUT/rolled_$n.bin"
  ct=()
  for _ in $(seq $REPS); do
    s=$(date +%s%N); fs_cc "$exe" "$c"; e=$(date +%s%N)
    ct+=( $(( (e-s)/1000 )) )
  done
  cm=$(python3 -c "print('%.3f' % ($(median "${ct[@]}")/1000.0))")
  rt=(); ec=0
  for _ in $(seq $REPS); do
    s=$(date +%s%N); "$exe" >/dev/null 2>&1; ec=$?; e=$(date +%s%N)
    rt+=( $(( (e-s)/1000 )) )
  done
  rm_=$(python3 -c "print('%.3f' % ($(median "${rt[@]}")/1000.0))")
  eb=$(stat -c %s "$exe" 2>/dev/null || echo 0)
  printf '%s,%s,%s,%s,%s,%s,%s\n' "$n" "$cb" "$eb" "$emit" "$cm" "$rm_" "$ec" \
    >> "$OUT/rolled_compcert.csv"
done
cat "$OUT/rolled_compcert.csv"
