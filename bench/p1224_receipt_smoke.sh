#!/usr/bin/env bash
# Non-vacuous smoke/control for both Proposition 12.2.4 receipt programs.
# Run the whole script in a no-swap cgroup, for example:
#
#   systemd-run --user --wait --collect --pipe --quiet \
#     --working-directory="$PWD" \
#     -p MemoryAccounting=yes -p MemoryMax=64G -p MemorySwapMax=0 \
#     bench/p1224_receipt_smoke.sh
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d /tmp/leancompcert-p1224-smoke.XXXXXX)
trap 'rm -rf "$work"' EXIT
cd "$root"

compile_and_time() {
  local src=$1 exe=$2 label=$3
  /usr/bin/time -f "$label compile wall=%e user=%U maxrss_kb=%M" \
    ccomp -O -o "$exe" "$src"
  /usr/bin/time -f "$label run wall=%e user=%U maxrss_kb=%M" "$exe"
}

# The row run covers q=1,...,32, hence includes q=30.  Its retained q=30
# words below seed a genuinely tested whole-prefix margin run.
lake env lean --run bench/Prop1224RowEmit.lean \
  1 32 1 32 4 32 "$work/row.c"
lake env lean --run bench/Prop1224RowEmit.lean \
  1 32 1 32 4 32 "$work/row_audit.c" audit

compile_and_time "$work/row.c" "$work/row" row > "$work/row.out" 2> "$work/row.time"
compile_and_time "$work/row_audit.c" "$work/row_audit" row-audit \
  > "$work/row_audit.out" 2> "$work/row_audit.time"
grep -qx 'verdict PASS' "$work/row.out"
grep -qx 'audit 0' "$work/row_audit.out"
grep -qx '30 8 3 69435208 69435218 45879730 17895697 219891810 60940086 583835921 9322' \
  "$work/row.out"
cat "$work/row.time" "$work/row_audit.time"

# q=30, r=1,...,20.  The row reports f1Hi=45879730; the compiled compact-row
# conversion proves and emits afHi=ceil(kAHi*f1Hi/2^E)=209640114 for the cell
# checker.  Starting at one makes the exact G carry zero; cells
# k=8,...,20 are tested.  The cube-root cursor is conservatively pre-seeded
# for the first tested cell, while EX=0, TH=2 is the exact logarithm seed.
cell_args=(30 17895697 219891810 209640114 8 9322 1 20 1
  0 0 2 1737 2,3,5)
lake env lean --run bench/Prop1224CellEmit.lean \
  "${cell_args[@]}" "$work/cell.c"
lake env lean --run bench/Prop1224CellEmit.lean \
  "${cell_args[@]}" "$work/cell_audit.c" audit

compile_and_time "$work/cell.c" "$work/cell" cell > "$work/cell.out" 2> "$work/cell.time"
compile_and_time "$work/cell_audit.c" "$work/cell_audit" cell-audit \
  > "$work/cell_audit.out" 2> "$work/cell_audit.time"
grep -qx 'slot1 13' "$work/cell.out"
grep -qx 'class margin 0' "$work/cell.out"
grep -qx 'verdict PASS' "$work/cell.out"
grep -qx 'audit 0' "$work/cell_audit.out"
cat "$work/cell.time" "$work/cell_audit.time"

# Discriminating control: an artificial initial G value of exactly 2^44 makes
# every tested margin fail, and must return the margin-specific code 6.
bad_args=(30 17895697 219891810 209640114 8 9322 1 20 1
  17592186044416 0 2 1737 2,3,5)
lake env lean --run bench/Prop1224CellEmit.lean \
  "${bad_args[@]}" "$work/cell_bad.c"
ccomp -O -o "$work/cell_bad" "$work/cell_bad.c"
set +e
"$work/cell_bad" > "$work/cell_bad.out"
status=$?
set -e
test "$status" -eq 6
grep -qx 'class margin 13' "$work/cell_bad.out"
grep -qx 'verdict FAIL margin' "$work/cell_bad.out"

# A maliciously high cube-root seed used to pass the old one-sided guard and
# shrink the reciprocal envelope.  It must now fail the lower-bound guard.
high_t_args=(30 17895697 219891810 209640114 8 9322 1 20 1
  0 0 2 2097152 2,3,5)
lake env lean --run bench/Prop1224CellEmit.lean \
  "${high_t_args[@]}" "$work/cell_high_t.c"
ccomp -O -o "$work/cell_high_t" "$work/cell_high_t.c"
set +e
"$work/cell_high_t" > "$work/cell_high_t.out"
status=$?
set -e
test "$status" -eq 5
grep -qx 'class guard_cuberoot_lower 13' "$work/cell_high_t.out"
grep -qx 'class margin 0' "$work/cell_high_t.out"
grep -qx 'verdict FAIL guard_cuberoot_lower' "$work/cell_high_t.out"

printf '%s\n' 'Prop1224 receipt smoke: PASS (row, audits, 13 margins, accumulator and cube-root controls)'
