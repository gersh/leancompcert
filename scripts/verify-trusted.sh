#!/usr/bin/env bash
# Full verification sequence for the opt-in artifact-run bridge.
#
# Run from the repository root.  Every step must pass; the axiom prints are the
# acceptance criterion and are meant to be read, not just exit-code checked.
set -euo pipefail

echo "== 1. build =="
lake build

echo
echo "== 2. native cross-check, forced (must be 0 cached) =="
lake exe lean-compcert check-native --force

echo
echo "== 3. zero-axiom gate: every certificate must show ONLY the base trio =="
lake env lean scripts/AxiomAudit.lean

echo
echo "== 4. where the new axiom may and may not appear =="
echo "   expected: base trio everywhere EXCEPT"
echo "     denote_of_evidence, Demo.demo_admitted"
echo "         -> LeanCompCert.Trusted.evidencedRun_sound"
echo "     returns_of_localReceipt{,_proved}, decide_of_localReceipt"
echo "         -> LeanCompCert.Trusted.localSignedRun_admits"
echo "   The two names are the two regimes.  A locally signed receipt is"
echo "   TAMPER-EVIDENT, not attested; see Trusted/LocalReceipt.lean."
lake env lean scripts/TrustedAxiomAudit.lean

echo
echo "== 5. no sorry, no native_decide in the opt-in modules =="
# Both words appear in the prose of these modules, always inside backticks;
# a real use never is.  So: match the words, then drop any line containing a
# backtick.
if grep -rn --include='*.lean' -E '\bsorry\b|\bnative_decide\b' \
     LeanCompCert/Trusted LeanCompCertTrusted.lean | grep -v '`'; then
  echo "FAIL: found a real sorry or native_decide"; exit 1
fi
echo "   clean"

echo
echo "== 6. the tactic, end to end (optional; needs ccomp and a run) =="
echo "   see tests/evidenced-decide/README.md"
