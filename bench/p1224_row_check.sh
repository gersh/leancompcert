#!/usr/bin/env bash
# Emit the per-q row artifact, compile it with gcc and (if present) ccomp, and
# compare every output slot against bench/ref_p1224.c on the same range.
#
#   bench/p1224_row_check.sh LO SEGLEN SEGCOUNT TABLEHI UNROLL [ROWS]
#
# The oracle prints one line per q — q phi omega Llo Lhi f1hi phi_lo const_lo
# kap_lo varpi_lo lam_hi — and a SUM line; the artifact prints the same eleven
# columns out of its per-row planes and the same SUM.  A single differing digit
# in any of them fails this script.
set -euo pipefail

LO=${1:-1}; LEN=${2:-256}; CNT=${3:-1}; THI=${4:-0}; UNR=${5:-8}
ROWS=${6:-$LEN}
HI=$((LO + LEN * CNT))
[ "$THI" -eq 0 ] && THI=$((HI - 1))

ROOT=$(cd "$(dirname "$0")/.." && pwd)
WORK=${P1224_WORK:-$(mktemp -d)}
mkdir -p "$WORK"
cd "$ROOT"

echo "== emitting  lo=$LO len=$LEN cnt=$CNT tableHi=$THI unroll=$UNR"
lake env lean --run bench/Prop1224RowEmit.lean \
  "$LO" "$LEN" "$CNT" "$THI" "$UNR" "$ROWS" "$WORK/row.c"

echo "== reference"
gcc -O2 -o "$WORK/ref" bench/ref_p1224.c -lm
"$WORK/ref" row "$LO" "$HI" > "$WORK/ref.all"
head -n "$ROWS" "$WORK/ref.all" > "$WORK/ref.rows"
grep '^SUM' "$WORK/ref.all" \
  | awk '{print "SUM", $2, $3, $4, $5, $6, $7, $8, $9, $10, $11}' > "$WORK/ref.sum"

status=0
for CC in gcc ccomp; do
  command -v "$CC" >/dev/null 2>&1 || { echo "-- $CC not found, skipped"; continue; }
  if [ "$CC" = gcc ]; then FLAGS="-O2"; else FLAGS="-O"; fi
  echo "== $CC $FLAGS"
  $CC $FLAGS -o "$WORK/row.$CC" "$WORK/row.c"
  /usr/bin/time -f "   %e s wall  %U s user  %M KB" "$WORK/row.$CC" > "$WORK/out.$CC" 2> "$WORK/time.$CC" \
    || { echo "   RUN FAILED"; status=1; continue; }
  cat "$WORK/time.$CC"
  head -n "$ROWS" "$WORK/out.$CC" > "$WORK/rows.$CC"
  grep '^SUM' "$WORK/out.$CC" > "$WORK/sum.$CC"
  if diff -q "$WORK/ref.rows" "$WORK/rows.$CC" >/dev/null; then
    echo "   rows: MATCH ($ROWS lines x 11 columns)"
  else
    echo "   rows: DIFFER"; diff "$WORK/ref.rows" "$WORK/rows.$CC" | head -20; status=1
  fi
  if diff -q "$WORK/ref.sum" "$WORK/sum.$CC" >/dev/null; then
    echo "   sum:  MATCH"
  else
    echo "   sum:  DIFFER"; diff "$WORK/ref.sum" "$WORK/sum.$CC"; status=1
  fi
  grep '^ROWS' "$WORK/out.$CC"
done
echo "work dir: $WORK"
exit $status
