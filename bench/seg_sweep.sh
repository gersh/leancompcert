#!/usr/bin/env bash
# Slot-for-slot agreement between the emitted artifact and bench/ref_seg.c,
# over a grid of (lo, segLen, segCount).
#
# The point is the corners.  `segLen` and `hi` both small drive the root phase
# into its degenerate cases -- a one-cell window, a bootstrap prime list of
# length one, a root sweep shorter than a single window -- and one of those
# corners silently produced wrong output before it was found by hand.  The
# grid below covers segLen from 1 to 10000 and hi from 3 to 10^10 + 10^6.
#
#   bench/seg_sweep.sh [CC]
#
# Prints one line per configuration and exits non-zero on the first
# disagreement.
set -u
CC=${1:-gcc}
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

gcc -O2 -o "$WORK/ref" bench/ref_seg.c || exit 2

fails=0
run() {
  local lo=$1 len=$2 cnt=$3 mode=$4
  lake env lean --run bench/ArraySegEmit.lean "$mode" "$lo" "$len" "$cnt" \
      "$WORK/a.c" - > "$WORK/emit.txt" 2>&1 || { cat "$WORK/emit.txt"; exit 2; }
  $CC -O2 -o "$WORK/a" "$WORK/a.c" || exit 2
  "$WORK/a" > "$WORK/got.txt" || exit 2
  "$WORK/ref" "$lo" "$len" "$cnt" > "$WORK/want.txt" || exit 2
  local pre; case "$mode" in mertens) pre=mertens;; *) pre=mobius;; esac
  local ok=1 i
  for i in 0 1 2; do
    local g w
    g=$(awk -v i="$i" '$1=="slot"i{print $2}' "$WORK/got.txt")
    w=$(awk -v p="$pre" -v i="$i" '$1==p && $2=="slot"i{print $3}' "$WORK/want.txt")
    [ "$g" = "$w" ] || ok=0
  done
  local info; info=$(grep -oP 'rootCount=\d+ rootLen=\d+ rootCap=\d+ boot=\d+' "$WORK/emit.txt")
  if [ "$ok" = 1 ]; then
    echo "ok   $mode lo=$lo L=$len S=$cnt  $info"
  else
    echo "FAIL $mode lo=$lo L=$len S=$cnt  $info"
    paste "$WORK/got.txt" "$WORK/want.txt" | head -4
    fails=$((fails + 1))
  fi
}

for mode in mertens platt211; do
  for len in 1 2 3 5 7 16 100 1000 10000; do
    for hi in 3 15 64 1000 100000; do
      cnt=$(( (hi + len - 1) / len )); [ "$cnt" -ge 1 ] || cnt=1
      run 1 "$len" "$cnt" "$mode"
    done
  done
  run 10000000000 1 5000 "$mode"
  run 10000000000 1000 1000 "$mode"
  run 10000000000 10000 100 "$mode"
  run 9999999999 7 1000 "$mode"
done

echo "sweep: $fails failures"
[ "$fails" = 0 ]
