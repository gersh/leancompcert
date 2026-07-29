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

mertens_cert_c="$output/mertens-cert.c"
mertens_cert_exe="$output/mertens-cert"
.lake/build/bin/lean-compcert emit-mertens-cert-c "$mertens_cert_c"
ccomp "$include_runtime" "$include_lean" \
  -o "$mertens_cert_exe" "$mertens_cert_c"
"$mertens_cert_exe"

wide_mertens_cert_c="$output/wide-mertens-cert.c"
wide_mertens_cert_exe="$output/wide-mertens-cert"
.lake/build/bin/lean-compcert emit-wide-mertens-cert-c "$wide_mertens_cert_c"
ccomp "$include_runtime" "$include_lean" \
  -o "$wide_mertens_cert_exe" "$wide_mertens_cert_c"
"$wide_mertens_cert_exe"

squarefree_cert_c="$output/squarefree-mertens-cert.c"
squarefree_cert_exe="$output/squarefree-mertens-cert"
.lake/build/bin/lean-compcert emit-squarefree-mertens-cert-c "$squarefree_cert_c"
ccomp "$include_runtime" "$include_lean" \
  -o "$squarefree_cert_exe" "$squarefree_cert_c"
"$squarefree_cert_exe"

fixedpoint_cert_c="$output/fixedpoint-cert.c"
fixedpoint_cert_exe="$output/fixedpoint-cert"
.lake/build/bin/lean-compcert emit-fixedpoint-cert-c "$fixedpoint_cert_c"
ccomp "$include_runtime" "$include_lean" \
  -o "$fixedpoint_cert_exe" "$fixedpoint_cert_c"
"$fixedpoint_cert_exe"

reflected_cert_c="$output/reflected-cert.c"
reflected_cert_exe="$output/reflected-cert"
.lake/build/bin/lean-compcert emit-reflected-cert-c "$reflected_cert_c"
ccomp "$include_runtime" "$include_lean" \
  -o "$reflected_cert_exe" "$reflected_cert_c"
"$reflected_cert_exe"

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

rolled_10m_c="$output/rolled-10m.c"
rolled_10m_exe="$output/rolled-10m"
.lake/build/bin/lean-compcert emit-rolled-10m-c "$rolled_10m_c"
ccomp "$include_runtime" "$include_lean" \
  -o "$rolled_10m_exe" "$rolled_10m_c"
"$rolled_10m_exe"

if command -v clightgen >/dev/null 2>&1; then
  for cert_c in "$verified_decide_c" "$mertens_cert_c" \
      "$wide_mertens_cert_c" "$squarefree_cert_c" \
      "$reflected_cert_c" "$fixedpoint_cert_c"; do
    clightgen "$include_runtime" "$include_lean" -normalize "$cert_c"
    cert_v="${cert_c%.c}.v"
    test -s "$cert_v"
  done
  echo "clightgen translation validation: all certificate units are Clight"
  python3 scripts/clight-correspond.py "$fixedpoint_cert_c" "${fixedpoint_cert_c%.c}.v"
  echo "clight structural correspondence: fixed-point certificate PASS"
  if [ -d /home/gersh/CompCert-3.17 ]; then
    python3 scripts/clight-correspond-coq.py "$fixedpoint_cert_c" \
      "${fixedpoint_cert_c%.c}.v" "$output/coq-correspond"
    echo "coq-kernel correspondence: fixed-point certificate Qed"
    direct_v="$output/DirectFP.v"
    rm -rf "$output/direct-verify"
    .lake/build/bin/lean-compcert emit-clight-fixedpoint-v "$direct_v"
    python3 scripts/clight-direct-verify.py "$direct_v" 40234404 \
      "$output/direct-verify" --self-test
    echo "direct Clight emission: CompCert bigstep semantics Qed at 40234404"
  else
    echo "CompCert Coq development not found; skipping kernel correspondence" >&2
  fi
else
  echo "clightgen not found; skipping Clight translation validation" >&2
fi

audit_log="$output/axiom-audit.txt"
lake env lean scripts/AxiomAudit.lean > "$audit_log"
test -s "$audit_log"
if grep -Eq "ofReduceBool|ofReduceNat|trustCompiler" "$audit_log"; then
  echo "error: native-evaluation axiom found in certificate audit" >&2
  exit 1
fi
echo "axiom audit clean: no native-evaluation axioms"

python3 -m unittest discover -s tests -v
echo "CompCert integration tests passed"
