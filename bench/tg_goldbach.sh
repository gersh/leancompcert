#!/usr/bin/env bash
# Measurement driver for the Helfgott--Platt Goldbach prime-ladder port.
#
#   bench/tg_goldbach.sh REFERENCE_CPP
#
# Reproduces, on this box, every number quoted in bench/results/tg_goldbach.md:
#
#   1. the reference producer's cost, split into stage (a) sieve,
#      stage (b) Proth test, and the rest;
#   2. the emitted stage-(a) sieve artifact -- rolled, so constant C size --
#      compiled with CompCert and with gcc, cross-checked against an
#      independent Python replay;
#   3. the emitted stage-(c) ladder-gap checker on the reference's own
#      delta stream, plus two fail-closed rejections.
#
# CPU (user) time is reported throughout: this box is shared.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/bench/results"
WORK="${TMPDIR:-/tmp}/tg_goldbach.$$"
REF="${1:?usage: tg_goldbach.sh REFERENCE_CPP}"
mkdir -p "$OUT" "$WORK"
cd "$ROOT"
INC="-Iruntime/include -I$(lean --print-prefix)/include"
ANCHOR=4000000000000000000

cpu() { /usr/bin/time -f '%U' "$@" 2>&1 >/dev/null | tail -1; }

# ---------------------------------------------------------------- reference
DIGEST=$(sha256sum "$REF" | cut -d' ' -f1)
g++ -std=c++20 -O2 \
  -DSPARKINTERVAL_TG_GOLDBACH_NATIVE_SOURCE_SHA256="\"$DIGEST\"" \
  -o "$WORK/ladder" "$REF" -lgmp || exit 1

printf 'range_exponent,user_s,records,candidates_sieved,proth_tests\n' \
  > "$OUT/tg_reference.csv"
for e in 22 23 24 25; do
  target=$(python3 -c "print(4*10**$e + $ANCHOR)")
  rm -f "$WORK/stream_$e"
  report=$("$WORK/ladder" --anchor-number $ANCHOR --target-number "$target" \
    --output "$WORK/stream_$e")
  python3 - "$e" "$report" >> "$OUT/tg_reference.csv" <<'PY'
import json, sys
e, report = sys.argv[1], json.loads(sys.argv[2])
print("%s,%s,%d,%d,%d" % (e, report["elapsed_seconds"],
    report["record_count"], report["candidates_sieved"],
    report["sieve_survivors_tested"]))
PY
done
cat "$OUT/tg_reference.csv"

# ------------------------------------------------------- stage (a) artifact
START=1000000000000
printf 'count,c_bytes,emit_s,ccomp_s,ccomp_run_ms,gcc_run_ms,exit\n' \
  > "$OUT/tg_sieve.csv"
for n in 20000 100000 500000; do
  value=$(python3 bench/tg_replay.py sieve $START "$n" |
    python3 -c "import json,sys;print(json.load(sys.stdin)['survivors'])")
  s=$(date +%s%N)
  lake env lean --run bench/TGSieveEmit.lean $START "$n" \
    "$WORK/s_$n.c" "$value" > /dev/null || continue
  e=$(date +%s%N); emit=$(( (e-s)/1000000 ))
  bytes=$(stat -c %s "$WORK/s_$n.c")
  s=$(date +%s%N); ccomp $INC -o "$WORK/s_$n.cc" "$WORK/s_$n.c" > /dev/null 2>&1
  e=$(date +%s%N); comp=$(( (e-s)/1000000 ))
  gcc -O2 $INC -o "$WORK/s_$n.gc" "$WORK/s_$n.c" > /dev/null 2>&1
  s=$(date +%s%N); "$WORK/s_$n.cc"; code=$?; e=$(date +%s%N)
  r1=$(( (e-s)/1000 ))
  s=$(date +%s%N); "$WORK/s_$n.gc"; e=$(date +%s%N); r2=$(( (e-s)/1000 ))
  printf '%s,%s,%s.%03d,%s.%03d,%s.%03d,%s.%03d,%s\n' "$n" "$bytes" \
    $((emit/1000)) $((emit%1000)) $((comp/1000)) $((comp%1000)) \
    $((r1/1000)) $((r1%1000)) $((r2/1000)) $((r2%1000)) "$code" \
    >> "$OUT/tg_sieve.csv"
done
cat "$OUT/tg_sieve.csv"

# ------------------------------------------------------- stage (c) artifact
python3 bench/tg_replay.py parse "$WORK/stream_23" "$WORK/deltas.txt" \
  > "$WORK/stream_23.json"
cat "$WORK/stream_23.json"
printf 'records,c_bytes,emit_s,ccomp_s,run_ms,exit\n' > "$OUT/tg_ladder.csv"
for n in 1000 5000 10275; do
  head -"$n" "$WORK/deltas.txt" > "$WORK/d_$n.txt"
  sum=$(python3 -c "print(sum(int(x) for x in open('$WORK/d_$n.txt')))")
  s=$(date +%s%N)
  lake env lean --run bench/TGLadderEmit.lean "$WORK/d_$n.txt" 888 "$sum" \
    "$WORK/l_$n.c" > /dev/null || continue
  e=$(date +%s%N); emit=$(( (e-s)/1000000 ))
  bytes=$(stat -c %s "$WORK/l_$n.c")
  s=$(date +%s%N); ccomp $INC -o "$WORK/l_$n.bin" "$WORK/l_$n.c" > /dev/null 2>&1
  e=$(date +%s%N); comp=$(( (e-s)/1000000 ))
  s=$(date +%s%N); "$WORK/l_$n.bin"; code=$?; e=$(date +%s%N); r=$(( (e-s)/1000 ))
  printf '%s,%s,%s.%03d,%s.%03d,%s.%03d,%s\n' "$n" "$bytes" \
    $((emit/1000)) $((emit%1000)) $((comp/1000)) $((comp%1000)) \
    $((r/1000)) $((r%1000)) "$code" >> "$OUT/tg_ladder.csv"
done
cat "$OUT/tg_ladder.csv"

# fail-closed: one delta pushed past the proved bound, and a wrong total
python3 - "$WORK/d_1000.txt" "$WORK/d_bad.txt" <<'PY'
import sys
lines = open(sys.argv[1]).read().split()
lines[len(lines) // 2] = "889"
open(sys.argv[2], "w").write("\n".join(lines) + "\n")
PY
sum=$(python3 -c "print(sum(int(x) for x in open('$WORK/d_1000.txt')))")
lake env lean --run bench/TGLadderEmit.lean "$WORK/d_bad.txt" 888 "$sum" \
  "$WORK/l_bad.c" > /dev/null
ccomp $INC -o "$WORK/l_bad.bin" "$WORK/l_bad.c" > /dev/null 2>&1
"$WORK/l_bad.bin"; echo "out-of-range delta -> exit $? (expect nonzero)"
lake env lean --run bench/TGLadderEmit.lean "$WORK/d_1000.txt" 888 \
  "$((sum + 1))" "$WORK/l_badsum.c" > /dev/null
ccomp $INC -o "$WORK/l_badsum.bin" "$WORK/l_badsum.c" > /dev/null 2>&1
"$WORK/l_badsum.bin"; echo "wrong running total -> exit $? (expect nonzero)"

rm -rf "$WORK"
