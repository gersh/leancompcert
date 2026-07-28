#!/bin/sh
set -eu

project_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$project_root"

output=".lake/build/integration/lcnf"
mkdir -p "$output/views" "$output/c"

lake build LeanCompCert.CompilerAdapter.Pass lean-compcert lean-compcert-tests
.lake/build/bin/lean-compcert-tests

LEAN_COMPCERT_LCNF_DIR="$project_root/$output/views" \
LEAN_COMPCERT_C_DIR="$project_root/$output/c" \
lake env lean \
  -o "$output/Capture.olean" \
  -i "$output/Capture.ilean" \
  -c "$output/Capture.lean.c" \
  tests/fixtures/Capture.lean

lean_prefix=$(lean --print-prefix)
include_runtime="-I$project_root/runtime/include"
include_lean="-I$lean_prefix/include"

ccomp "$include_runtime" "$include_lean" -c \
  -o "$output/captureAdd.o" "$output/c/l_captureAdd.c"
ccomp "$include_runtime" "$include_lean" -c \
  -o "$output/captureSelect.o" "$output/c/l_captureSelect.c"
ccomp -o "$output/lcnf-integration" \
  tests/integration/lcnf_harness.c \
  "$output/captureAdd.o" \
  "$output/captureSelect.o"
"$output/lcnf-integration"

verified_decide_c="$output/verified-decide.c"
verified_decide_exe="$output/verified-decide"
.lake/build/bin/lean-compcert emit-verified-decide-c "$verified_decide_c"
ccomp "$include_runtime" "$include_lean" \
  -o "$verified_decide_exe" "$verified_decide_c"
"$verified_decide_exe"

./bin/lean-compcert-probe tests/fixtures/Hello.lean \
  --output "$output/probe" \
  --attempt-rewrites \
  --differential-check

./bin/lean-compcert doctor
./bin/lean-compcert check-runtime \
  --output "$output/runtime-check"
./bin/lean-compcert compile-ir tests/fixtures/Capture.lean \
  --output "$output/driver-lcnf"
./bin/lean-compcert emit-c tests/fixtures/Hello.lean \
  --output "$output/driver-emit"
./bin/lean-compcert build tests/fixtures/Acceptance.lean \
  --output "$output/acceptance"
./bin/lean-compcert build tests/fixtures/AllocationStress.lean \
  --output "$output/allocation-stress"

python3 -m unittest discover -s tests -v
echo "CompCert integration tests passed"
