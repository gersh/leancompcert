#!/usr/bin/env bash
# Chain the offset segmented sieve over a geometric window schedule.
#
# Each window is one artifact: its thresholds are the reduced family's
# majorant evaluated at the window's worst endpoint, and its carry-in is the
# previous window's carry-out, read out of the result cells.  The ratio
# controls how much the fixed-per-window threshold gives away against the
# n-dependent majorant: a window [lo, hi] weakens an increasing majorant by
# sqrt(hi/lo) - 1, so ratio 1.05 costs 2.5%.
#
#   bench/seg_chain.sh MODE LO HI RATIO SEGLEN [CC]
#
# MODE is mertens (b = 755/1e4) or mertens2 (b = 285/1e4) or platt211 or
# plattstrong.  CC is the compiler for the artifacts, default gcc.
#
# Prints one line per window and exits non-zero on the first window whose
# artifact reports a failed threshold test.
set -u
MODE=${1:-mertens}; LO=${2:-9243}; HI=${3:-10000000}
RATIO=${4:-1.05}; SEGLEN=${5:-100000}; CC=${6:-gcc}
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# carry-in: neutral biases (the sweep starts at n = 1 conceptually, so a
# genuine chain must be primed by a first window that starts at 1).
SEEDS=""
if [ "$LO" -gt 1 ]; then
  prime_cnt=$(python3 -c "print(max(1, -(-($LO-1)//$SEGLEN)))")
  lake env lean --run bench/ArraySegEmit.lean "$MODE" 1 "$SEGLEN" "$prime_cnt" \
      "$WORK/p.c" - > "$WORK/pe.txt" 2>&1 || { cat "$WORK/pe.txt"; exit 2; }
  $CC -O2 -o "$WORK/p" "$WORK/p.c" || exit 2
  "$WORK/p" > "$WORK/pout.txt" || exit 2
  p0=$(awk '/^slot0/{print $2}' "$WORK/pout.txt")
  p1=$(awk '/^slot1/{print $2}' "$WORK/pout.txt")
  p2=$(awk '/^slot2/{print $2}' "$WORK/pout.txt")
  prime_hi=$(awk '/^mode=/{print $NF}' "$WORK/pe.txt" | sed 's/hi=//')
  echo "prime  [1, $prime_hi] (thresholds ignored)"
  case "$MODE" in
    platt211|plattstrong) SEEDS="$p0" ;;
    *)                    SEEDS="$p0 $p1 $p2" ;;
  esac
  LO=$((prime_hi + 1))
fi
lo=$LO
total_viol=0
while [ "$lo" -le "$HI" ]; do
  hi=$(python3 -c "print(min($HI, max($lo+$SEGLEN-1, int($lo*$RATIO))))")
  cnt=$(python3 -c "print(max(1, -(-($hi-$lo+1)//$SEGLEN)))")
  # shellcheck disable=SC2086
  lake env lean --run bench/ArraySegEmit.lean "$MODE" "$lo" "$SEGLEN" "$cnt" \
      "$WORK/w.c" - $SEEDS > "$WORK/emit.txt" 2>&1 || { cat "$WORK/emit.txt"; exit 2; }
  $CC -O2 -o "$WORK/w" "$WORK/w.c" || exit 2
  "$WORK/w" > "$WORK/out.txt" || exit 2
  viol=$(awk '/^violations/{print $2}' "$WORK/out.txt")
  s0=$(awk '/^slot0/{print $2}' "$WORK/out.txt")
  s1=$(awk '/^slot1/{print $2}' "$WORK/out.txt")
  s2=$(awk '/^slot2/{print $2}' "$WORK/out.txt")
  real_hi=$(awk '/^mode=/{print $NF}' "$WORK/emit.txt" | sed 's/hi=//')
  echo "window [$lo, $real_hi] segments=$cnt violations=$viol"
  total_viol=$((total_viol + viol))
  if [ "$viol" != "0" ]; then
    echo "FAILED at window [$lo, $real_hi]"; sed -n '1,8p' "$WORK/out.txt"; exit 1
  fi
  case "$MODE" in
    platt211|plattstrong) SEEDS="$s0" ;;
    *)                    SEEDS="$s0 $s1 $s2" ;;
  esac
  lo=$((real_hi + 1))
done
echo "chain complete: $MODE over [$LO, $HI], total violations $total_viol"
