#!/usr/bin/env bash
# Emit, compile and run the Ramare `c_E` dyadic-tail artifacts, with
# discrimination controls in both directions.
#
#   bench/ce_dyadic.sh smoke      -- the 20000-candidate window, both directions
#   bench/ce_dyadic.sh scale      -- the production ranges (ce is ~10 min)
#
# Every run records the command, the exit status, the wall clock and the
# sha256 of the C.  The BINARY digest is recorded too but it names one build:
# two identical `ccomp -O2` invocations on the same C do not agree.
#
# The controls are the point.  A certificate artifact that exits 0 says
# nothing unless a WRONG input on the SAME range exits nonzero, so each
# instance is run twice: once at its real bound, once one unit past it in the
# direction that must fail.  `ce` accepts on `bound <= acc`, so its negative
# control raises the bound by one; `ceU` accepts on `acc <= bound`, so its
# negative control lowers the bound by one.
set -euo pipefail
cd "$(dirname "$0")/.."
OUT=${OUT:-/tmp/ce_dyadic}
mkdir -p "$OUT"

emit_run () {                   # tag lo len R k0 up lfx bound expect
  local tag=$1 lo=$2 len=$3 R=$4 k0=$5 up=$6 lfx=$7 bound=$8 expect=$9
  local c="$OUT/$tag.c" bin="$OUT/$tag.bin"
  echo "--- $tag : LO=$lo LEN=$len R=$R K0=$k0 UP=$up LFX=$lfx BOUND=$bound"
  lake env lean --run bench/CeDyadicEmit.lean "$lo" "$len" "$R" "$k0" "$up" \
    "$lfx" "$bound" "$c"
  echo "    c_sha256   $(sha256sum "$c" | cut -d' ' -f1)"
  ccomp -O2 "$c" -o "$bin"
  echo "    bin_sha256 $(sha256sum "$bin" | cut -d' ' -f1)  (one build only)"
  local t0 t1 status
  t0=$(date +%s.%N)
  set +e; "$bin"; status=$?; set -e
  t1=$(date +%s.%N)
  echo "    run_cmd    $bin"
  echo "    exit       $status   (expected $expect)"
  echo "    wall       $(echo "$t1 - $t0" | bc) s"
  if [ "$status" != "$expect" ]; then
    echo "    *** CONTROL FAILED ***"; exit 1
  fi
}

LFX_LO=12786308640407511063
LFX_UP=12786308649630883101

case "${1:-smoke}" in
  smoke)
    # window [20001, 40000]; machine totals 460801813696337 / 460806880485962
    emit_run ce_smoke_pos    20001 20000 2501 14 0 $LFX_LO 460801813696337 0
    emit_run ce_smoke_neg    20001 20000 2501 14 0 $LFX_LO 460801813696338 1
    emit_run ceu_smoke_pos   20001 20000 2501 14 1 $LFX_UP 460806880485962 0
    emit_run ceu_smoke_neg   20001 20000 2501 14 1 $LFX_UP 460806880485961 1
    ;;
  scale)
    # ce  : [20001, 25000000], true acc 920304960095878, certified bound below it
    # ceU : [20001,   200000], true acc 828905072852048, certified bound EQUAL
    emit_run ceu_scale_pos   20001 180000   2501 14 1 $LFX_UP 828905072852048 0
    emit_run ceu_scale_neg   20001 180000   2501 14 1 $LFX_UP 828905072852047 1
    emit_run ce_scale_pos    20001 24980000 2501 14 0 $LFX_LO 920304943318662 0
    emit_run ce_scale_neg    20001 24980000 2501 14 0 $LFX_LO 920304960095879 1
    ;;
  *) echo "usage: $0 [smoke|scale]"; exit 2;;
esac
echo "ALL CONTROLS PASSED"
