#!/usr/bin/env bash
# Chain the per-integer `Σ μ(m)/m` artifact (`plattstronglive`) over [1, HI].
#
#   bench/moblive_chain.sh HI SEGLEN LINKLEN [CC] [MANIFEST] [--corrupt K]
#
# SEGLEN  cells per sieve window -- a memory parameter only.
# LINKLEN integers per artifact; must be a multiple of SEGLEN.  One link is one
#         emitted, compiled, executed C program.
#
# The chain always opens at n = 1, because that is the only carry-in that is
# not a hand-computed number: the accumulator is the bare bias.  The first link
# must therefore report exactly FIRSTVIOL = 3 failed tests, and every later
# link exactly 0.  The three are known, and none of them is a defect:
#
#   n = 1  the family is false: the sum is 1, the majorant 1/(2√2) = 0.354;
#   n = 2  the family is false: 1/2 against 1/(2√3) = 0.289;
#   n = 4  an exact tie the test cannot resolve.  Σ_{m≤4} μ(m)/m = 1/6 and
#          ⌈√5⌉ = 3, so |V| lands exactly on ⌊2⁶¹/3⌋ and the +1 for the shift's
#          truncation tips it over.  The family holds there with enormous room
#          (1/6 against 1/(2√5) = 0.224); it is the ⌈·⌉ relaxation, which costs
#          a relative 1/√(n+1), being coarse at a tiny n.  Swept exhaustively,
#          n = 4 is the ONLY integer in [3, 7.727·10⁹] where the relaxation
#          costs anything -- see bench/results/array_seg_folds.md.
#
# Both counts are asserted.  A first link reporting 0 would mean the artifact
# was not testing what it claims.
#
# WHAT IS DIFFERENT FROM bench/seg_chain.sh, AND WHY IT MATTERS
#
# 1. No window schedule.  The artifact tests `|Σ_{m≤n} μ(m)/m| ≤ 1/(2√(n+1))`
#    at every integer against `⌊2⁶¹/⌈√(n+1)⌉⌋`, so a window is a unit of memory
#    and the `√(hi/lo) − 1` loss of a geometric schedule is gone.  The last
#    link is clamped so the chain stops at exactly HI, which is the fourth
#    hazard of seg_chain.sh -- overshooting past the range the family claims --
#    made structurally impossible.
#
# 2. The exit code is not the check.  seg_chain.sh accepts a window when the
#    artifact reports zero violations.  That is not sound for a *chain*: a
#    window run with the wrong carry-in computes a wrong accumulator, and a
#    wrong accumulator can perfectly well stay under the threshold and report
#    zero.  Zero violations proves nothing about a link whose input was not the
#    previous link's output.
#
#    So every link is checked on ALL FIVE numbers it produces -- the violation
#    count and the four result slots (the two accumulator limbs, ⌈√(hi+1)⌉ and
#    its square) -- against a manifest, and the seed handed to link i is,
#    literally, the two slots link i−1 printed.  A chain is accepted only when
#    every link reproduces the manifest exactly, every link reports the
#    expected count, and the last link ends at HI.
#
#    `--corrupt K` perturbs the carry-in of link K by one ulp.  Run it against a
#    good manifest to see the difference: the artifact still reports zero
#    violations -- the old check passes -- and the manifest comparison rejects.
#
# 3. The seed is not free.  The extremum residue can be run with a zero carry-in
#    in any order and reconciled afterwards; this one cannot, because the
#    threshold is applied inside the loop.  The chain is serial.
set -u

HI=${1:-100000000}
SEGLEN=${2:-1000000}
LINKLEN=${3:-$HI}
CC=${4:-gcc}
MANIFEST=${5:-}
CORRUPT=-1
if [ "${6:-}" = "--corrupt" ]; then CORRUPT=${7:-1}; fi
FIRSTVIOL=3   # n = 1, 2 (family false) and n = 4 (an exact tie); see above

if [ $((LINKLEN % SEGLEN)) -ne 0 ]; then
  echo "LINKLEN ($LINKLEN) must be a multiple of SEGLEN ($SEGLEN)"; exit 2
fi

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# `mobWideBits = 15`, so the accumulator opens at the bare bias 2^(64+15):
# low limb 0, high limb 2^15 = 32768.
TLO=0
THI=32768

NEW=""
if [ -n "$MANIFEST" ] && [ ! -f "$MANIFEST" ]; then NEW=yes; : > "$MANIFEST"; fi

lo=1
link=0
fail=0
while [ "$lo" -le "$HI" ]; do
  link=$((link + 1))
  span=$((HI - lo + 1))
  if [ "$span" -ge "$LINKLEN" ]; then
    len=$SEGLEN; cnt=$((LINKLEN / SEGLEN))
  elif [ $((span % SEGLEN)) -eq 0 ]; then
    len=$SEGLEN; cnt=$((span / SEGLEN))
  else
    len=$span; cnt=1
  fi

  seedlo=$TLO; seedhi=$THI
  if [ "$CORRUPT" = "$link" ]; then
    # +1 ulp, in *unsigned* 64-bit arithmetic -- bash's $(( )) is signed and
    # would wrap a limb above 2^63 into a gross error, which is exactly the
    # kind of corruption the old check would have caught anyway.  One ulp at
    # scale 2^78 is 2^-78 in the sum: far below any threshold.
    seedlo=$(python3 -c "print(($seedlo + 1) % 2**64)")
    echo "link $link: carry-in DELIBERATELY CORRUPTED (+1 ulp on the low limb)"
  fi

  lake env lean --run bench/ArraySegEmit.lean plattstronglive \
      "$lo" "$len" "$cnt" "$WORK/w.c" - "$seedlo" "$seedhi" \
      > "$WORK/emit.txt" 2>&1 || { cat "$WORK/emit.txt"; exit 2; }
  $CC -O2 -o "$WORK/w" "$WORK/w.c" || exit 2
  "$WORK/w" > "$WORK/out.txt" || exit 2

  viol=$(awk '/^violations/{print $2}' "$WORK/out.txt")
  s0=$(awk '/^slot0/{print $2}' "$WORK/out.txt")
  s1=$(awk '/^slot1/{print $2}' "$WORK/out.txt")
  s2=$(awk '/^slot2/{print $2}' "$WORK/out.txt")
  s3=$(awk '/^slot3/{print $2}' "$WORK/out.txt")
  real_hi=$(awk '/^mode=/{print $NF}' "$WORK/emit.txt" | sed 's/hi=//')

  line="$lo $real_hi $viol $s0 $s1 $s2 $s3"
  echo "link $link: [$lo, $real_hi] seed=($seedlo,$seedhi) violations=$viol slots=($s0,$s1,$s2,$s3)"

  if [ -n "$MANIFEST" ]; then
    if [ -n "$NEW" ]; then
      echo "$line" >> "$MANIFEST"
    else
      want=$(sed -n "${link}p" "$MANIFEST")
      if [ "$want" != "$line" ]; then
        echo "MANIFEST MISMATCH at link $link"
        echo "  expected: $want"
        echo "  got:      $line"
        fail=1
      fi
    fi
  fi

  if [ "$link" = "1" ]; then want_viol=$FIRSTVIOL; else want_viol=0; fi
  if [ "$viol" != "$want_viol" ]; then
    echo "VIOLATION COUNT $viol at link $link, range [$lo, $real_hi] (wanted $want_viol)"
    fail=1
  fi

  TLO=$s0; THI=$s1
  lo=$((real_hi + 1))
done

if [ "$lo" != "$((HI + 1))" ]; then
  echo "ENDPOINT MISMATCH: chain stopped after $((lo - 1)), wanted $HI"; fail=1
fi

if [ "$fail" != "0" ]; then
  echo "chain REJECTED"
  exit 1
fi
echo "chain accepted: [1, $HI], $link links, failures only at n = 1, 2, 4, manifest reproduced"
