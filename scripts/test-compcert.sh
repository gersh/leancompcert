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

# Only Lean-generated C (the LCNF harness objects below) needs <lean/lean.h>
# and hence the <stdatomic.h> shim.  The emitted certificate units include
# just <stdint.h>/<stddef.h> and are compiled with no -I at all.
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
ccomp -o "$verified_decide_exe" "$verified_decide_c"
"$verified_decide_exe"

mertens_cert_c="$output/mertens-cert.c"
mertens_cert_exe="$output/mertens-cert"
.lake/build/bin/lean-compcert emit-mertens-cert-c "$mertens_cert_c"
ccomp -o "$mertens_cert_exe" "$mertens_cert_c"
"$mertens_cert_exe"

wide_mertens_cert_c="$output/wide-mertens-cert.c"
wide_mertens_cert_exe="$output/wide-mertens-cert"
.lake/build/bin/lean-compcert emit-wide-mertens-cert-c "$wide_mertens_cert_c"
ccomp -o "$wide_mertens_cert_exe" "$wide_mertens_cert_c"
"$wide_mertens_cert_exe"

squarefree_cert_c="$output/squarefree-mertens-cert.c"
squarefree_cert_exe="$output/squarefree-mertens-cert"
.lake/build/bin/lean-compcert emit-squarefree-mertens-cert-c "$squarefree_cert_c"
ccomp -o "$squarefree_cert_exe" "$squarefree_cert_c"
"$squarefree_cert_exe"

fixedpoint_cert_c="$output/fixedpoint-cert.c"
fixedpoint_cert_exe="$output/fixedpoint-cert"
.lake/build/bin/lean-compcert emit-fixedpoint-cert-c "$fixedpoint_cert_c"
ccomp -o "$fixedpoint_cert_exe" "$fixedpoint_cert_c"
"$fixedpoint_cert_exe"

reflected_cert_c="$output/reflected-cert.c"
reflected_cert_exe="$output/reflected-cert"
.lake/build/bin/lean-compcert emit-reflected-cert-c "$reflected_cert_c"
ccomp -o "$reflected_cert_exe" "$reflected_cert_c"
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
ccomp -o "$rolled_10m_exe" "$rolled_10m_c"
"$rolled_10m_exe"

native_check_dir="$output/native-check"
rm -rf "$native_check_dir"
.lake/build/bin/lean-compcert check-native --dir "$native_check_dir"
native_second=$(.lake/build/bin/lean-compcert check-native --dir "$native_check_dir")
case "$native_second" in
  *"[run]"*)
    echo "native check change tracking failed: second run recompiled" >&2
    exit 1
    ;;
esac
echo "native check: all certificates pass; change tracking verified (second run fully cached)"

if command -v clightgen >/dev/null 2>&1; then
  for cert_c in "$verified_decide_c" "$mertens_cert_c" \
      "$wide_mertens_cert_c" "$squarefree_cert_c" \
      "$reflected_cert_c" "$fixedpoint_cert_c"; do
    clightgen -normalize "$cert_c"
    cert_v="${cert_c%.c}.v"
    test -s "$cert_v"
  done
  echo "clightgen translation validation: all certificate units are Clight"
  python3 scripts/clight-correspond.py "$fixedpoint_cert_c" "${fixedpoint_cert_c%.c}.v"
  echo "clight structural correspondence: fixed-point certificate PASS"
  compcert_coq_dir="${COMPCERT_DIR:-/home/gersh/CompCert-3.17}"
  if [ -d "$compcert_coq_dir" ]; then
    COMPCERT_DIR="$compcert_coq_dir"
    export COMPCERT_DIR
    python3 scripts/clight-correspond-coq.py "$fixedpoint_cert_c" \
      "${fixedpoint_cert_c%.c}.v" "$output/coq-correspond"
    echo "coq-kernel correspondence: fixed-point certificate Qed"
    direct_v="$output/DirectFP.v"
    rm -rf "$output/direct-verify"
    .lake/build/bin/lean-compcert emit-clight-fixedpoint-v "$direct_v"
    python3 scripts/clight-direct-verify.py "$direct_v" 40234404 \
      "$output/direct-verify" --self-test
    echo "direct Clight emission: CompCert bigstep semantics Qed at 40234404"
    array_c="$native_check_dir/mobius-array.c"
    clightgen -normalize "$array_c"
    python3 scripts/clight-array-verify.py "${array_c%.c}.v" \
      f_l_ArrayMobius_rolled100k "$output/array-direct-verify"
    echo "production array Clight AST: rolled/memory endpoint Qed"
  else
    echo "CompCert Coq development not found; skipping kernel correspondence" >&2
  fi
else
  echo "clightgen not found; skipping Clight translation validation" >&2
fi

# The run-receipt loop, end to end: generate a local key, attest one
# certificate, verify the receipt against freshly emitted C, and require that a
# receipt with ONE edited field is rejected.  The last step is the whole point
# of signing: without it a receipt is a text file anyone can rewrite.
attest_dir="$output/attest"
rm -rf "$attest_dir"
mkdir -p "$attest_dir"
.lake/build/bin/lean-compcert attest-keygen --key "$attest_dir/key.pem" >/dev/null
.lake/build/bin/lean-compcert attest \
  --key "$attest_dir/key.pem" \
  --dir "$attest_dir/check" \
  --receipts "$attest_dir/receipts" \
  --campaign "acceptance" >/dev/null
test -s "$attest_dir/receipts/rolled-10m.receipt"
.lake/build/bin/lean-compcert verify-receipt \
  "$attest_dir/receipts/rolled-10m.receipt" --cert rolled-10m >/dev/null
# A receipt that names another certificate's program must not verify.
if .lake/build/bin/lean-compcert verify-receipt \
     "$attest_dir/receipts/rolled-10m.receipt" --cert fixedpoint >/dev/null 2>&1; then
  echo "receipt bound to the wrong certificate was accepted" >&2
  exit 1
fi
# One edited field must break the signature.
sed 's/^acceptance$/acceptance-tampered/' \
  "$attest_dir/receipts/rolled-10m.receipt" > "$attest_dir/tampered.receipt"
if .lake/build/bin/lean-compcert verify-receipt \
     "$attest_dir/tampered.receipt" --cert rolled-10m >/dev/null 2>&1; then
  echo "a receipt edited after signing was accepted" >&2
  exit 1
fi
echo "run receipts: signed, verified, and both substitution and tampering rejected"

audit_log="$output/axiom-audit.txt"
lake env lean scripts/AxiomAudit.lean > "$audit_log"
test -s "$audit_log"
# Allowlist check: every audited theorem may depend only on the three
# standard axioms.  This also rejects `sorryAx` and any bespoke axiom, not
# just the native-evaluation axioms.
python3 - "$audit_log" <<'EOF'
import re
import sys

allowed = {"propext", "Classical.choice", "Quot.sound"}
text = open(sys.argv[1]).read()
entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
if not entries:
    sys.exit("error: axiom audit output had no parseable axiom reports")
bad = [
    (name, axiom)
    for name, axioms in entries
    for axiom in (a.strip() for a in axioms.split(","))
    if axiom and axiom not in allowed
]
for name, axiom in bad:
    print(f"error: {name} depends on non-allowlisted axiom {axiom}",
          file=sys.stderr)
if bad:
    sys.exit(1)
print(f"axiom audit clean: {len(entries)} theorems, "
      "axioms within {propext, Classical.choice, Quot.sound}")
EOF

# The axiom PARTITION gate.
#
# The recurring public objection to this package is "you say it will have no
# axioms; I don't understand how that is possible".  The answer is that the
# claim is a partition, not a blanket, and this gate is its mechanical form:
#
#   * `LeanCompCert`        — zero axioms beyond the three standard ones.  The
#                             kernel route never runs a compiler, so there is
#                             nothing to admit.  Checked by the block above.
#   * `LeanCompCertTrusted` — exactly TWO further axioms, by name, one per
#                             admission regime.  Anything else appearing here
#                             is a silent widening of the trusted base and
#                             fails the build.
trusted_log="$output/trusted-axiom-audit.txt"
lake env lean scripts/TrustedAxiomAudit.lean > "$trusted_log"
test -s "$trusted_log"
python3 - "$trusted_log" <<'EOF'
import re
import sys

standard = {"propext", "Classical.choice", "Quot.sound"}
# The admitted schemas, and the per-use-site axioms the tactic mints, which
# are all instances of exactly one of those statements.  The two regimes are
# named apart on purpose: a reader of a downstream `#print axioms` must be able
# to tell "an evidenced artifact run" from "a receipt the running machine
# signed about itself" without reading any source.
admitted = {
    "LeanCompCert.Trusted.evidencedRun_sound",
    "LeanCompCert.Trusted.localSignedRun_admits",
}
text = open(sys.argv[1]).read()
entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
if not entries:
    sys.exit("error: trusted axiom audit output had no parseable axiom reports")

bad = []
carriers = set()
for name, axioms in entries:
    for axiom in (a.strip() for a in axioms.split(",")):
        if not axiom or axiom in standard:
            continue
        if axiom in admitted or axiom.endswith("._evidenced.run.ax"):
            carriers.add(name)
            continue
        bad.append((name, axiom))

for name, axiom in bad:
    print(f"error: {name} depends on unexpected trusted axiom {axiom}",
          file=sys.stderr)
if bad:
    sys.exit(1)
print(f"axiom partition clean: {len(entries)} audited; "
      f"{len(carriers)} declaration(s) carry one of {sorted(admitted)}; "
      "no other axiom present")
EOF

python3 -m unittest discover -s tests -v
echo "CompCert integration tests passed"
