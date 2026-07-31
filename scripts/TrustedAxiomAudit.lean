import LeanCompCertTrusted
import LeanCompCert.Testing.MertensCertificate
import LeanCompCert.Testing.ArraySegCertificate

/-!
Axiom-audit gate for the **opt-in** artifact-run bridge.

`scripts/AxiomAudit.lean` is the zero-axiom gate: every declaration it prints
must show `[propext, Classical.choice, Quot.sound]` and nothing else.  This
file is its counterpart, and it exists so that the *presence* of the new axiom
is pinned to exactly the places it is supposed to be.

Expected output, and the acceptance criterion:

* everything in `LeanCompCert.Trusted` that is *checker* code — `verify`'s
  negative theorems, the concrete refusals — prints the base trio.  The checker
  must not depend on the thing it is checking.
* exactly one family of declarations prints
  `LeanCompCert.Trusted.evidencedRun_sound`: the schema wrapper
  `denote_of_evidence` and the one demonstration that uses it.
* the pre-existing certificates print the base trio, unchanged.  That is the
  regression check that matters: adding an opt-in axiom must not leak into a
  consumer who did not ask for it.

A use site closed by the `evidenced_decide` tactic prints
`<declaration>._evidenced.run.ax` instead — one entry per admitted execution.
There are none in this build, because the tactic reads evidence produced out of
band and a fresh checkout has none; see `tests/evidenced-decide/`.
-/

-- The checker itself: axiom-free, or it would be checking nothing.
#print axioms LeanCompCert.Trusted.verify_tdxAttested
#print axioms LeanCompCert.Trusted.verify_binds_value
#print axioms LeanCompCert.Trusted.verify_binds_identity
#print axioms LeanCompCert.Trusted.verify_binds_nonce
#print axioms LeanCompCert.Trusted.verify_cached_has_no_nonce
#print axioms LeanCompCert.Trusted.verify_agrees
#print axioms LeanCompCert.Trusted.verify_wellFormed
#print axioms LeanCompCert.Trusted.verify_false_of_value_ne
#print axioms LeanCompCert.Trusted.verify_false_of_digest_ne
#print axioms LeanCompCert.Trusted.verify_false_of_machine_ne
#print axioms LeanCompCert.Trusted.verify_false_of_illFormed
#print axioms LeanCompCert.Trusted.verify_false_of_nonce_ne
#print axioms LeanCompCert.Trusted.verify_false_of_cached_nonce
#print axioms LeanCompCert.Trusted.verify_false_of_verdict_ne

-- The concrete refusals, and the positive control.
#print axioms LeanCompCert.Trusted.Demo.demo_denote
#print axioms LeanCompCert.Trusted.Demo.cached_accepted
#print axioms LeanCompCert.Trusted.Demo.fresh_accepted
#print axioms LeanCompCert.Trusted.Demo.refuse_wrong_artifact
#print axioms LeanCompCert.Trusted.Demo.refuse_wrong_machine
#print axioms LeanCompCert.Trusted.Demo.refuse_wrong_nonce
#print axioms LeanCompCert.Trusted.Demo.refuse_cached_claiming_nonce
#print axioms LeanCompCert.Trusted.Demo.refuse_truncated_digest
#print axioms LeanCompCert.Trusted.Demo.refuse_empty_machine
#print axioms LeanCompCert.Trusted.Demo.refuse_wrong_value
#print axioms LeanCompCert.Trusted.Demo.binds_this_program
#print axioms LeanCompCert.Trusted.Demo.refuse_wrong_program
#print axioms LeanCompCert.Trusted.Demo.refuse_disagrees
#print axioms LeanCompCert.Trusted.Demo.refuse_abnormal
#print axioms LeanCompCert.Trusted.Demo.refuse_bad_shard
#print axioms LeanCompCert.Trusted.Demo.refuse_tdx

-- The two declarations that DO carry the axiom, and nothing else does.
#print axioms LeanCompCert.Trusted.denote_of_evidence
#print axioms LeanCompCert.Trusted.Demo.demo_admitted

-- Regression: pre-existing certificates are untouched by all of the above.
#print axioms LeanCompCert.Testing.MertensCertificate.referenceSum_eq
#print axioms LeanCompCert.Ports.ArraySegSieve.mertensProgram_compiled
