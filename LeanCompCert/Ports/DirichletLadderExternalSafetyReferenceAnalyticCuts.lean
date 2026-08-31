import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceZeroDecode

/-! Source-shaped projections of the decoded transcript for later analytic
interpretation.  These are deliberately named *integer* checks: they do not
assert that a bitmap bit is a true Dirichlet-L sign or that the roster is
mathematically complete. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert.Ports.DirichletLadder

theorem noFailures_take {conditions : List Bool} (n : Nat)
    (h : NoFailures conditions) : NoFailures (conditions.take n) := by
  intro b hb
  exact h b (List.mem_of_mem_take hb)

theorem noFailures_drop {conditions : List Bool} (n : Nat)
    (h : NoFailures conditions) : NoFailures (conditions.drop n) := by
  intro b hb
  exact h b (List.mem_of_mem_drop hb)

/-- Bitmap/digest and endpoint-parity flags (conditions 16 and 17), plus the
terminal digest equality. -/
structure DecodedSignBitmapIntegerChecks (c : Cfg) (words : List Nat) : Prop where
  perRecord : ∀ idx, idx < c.records →
    NoFailures
      (((referenceConditions c words (referenceStateAt c words idx) idx).drop
        15).take 2)
  terminalDigest : (referenceStateAt c words c.records).prevDig = c.termDigest

/-- Integer Turing/height window checks: slot count and closing-window flags
9 through 20, retaining the exact multiplicity-bearing transition and moment
arithmetic. -/
structure DecodedTuringIntegerChecks (c : Cfg) (words : List Nat) : Prop where
  perRecord : ∀ idx, idx < c.records →
    NoFailures
      (((referenceConditions c words (referenceStateAt c words idx) idx).drop
        8).take 12)
  terminalLast : (referenceStateAt c words c.records).prevLast = 1

/-- Integer roster linkage checks: conjugate constancy (21) and the two
first-record pointer/address checks (24--25).  Completeness among mathematical
primitive characters remains a separate source-shaped premise. -/
structure DecodedRosterIntegerChecks (c : Cfg) (words : List Nat) : Prop where
  conjugate : ∀ idx, idx < c.records →
    NoFailures
      (((referenceConditions c words (referenceStateAt c words idx) idx).drop
        20).take 1)
  firstPointer : ∀ idx, idx < c.records →
    NoFailures
      ((referenceConditions c words (referenceStateAt c words idx) idx).drop 23)

theorem DecodedReferenceTranscript.signBitmapIntegerChecks
    {c : Cfg} {words : List Nat} (h : DecodedReferenceTranscript c words) :
    DecodedSignBitmapIntegerChecks c words := {
  perRecord := by
    intro idx hidx
    exact noFailures_take 2 (noFailures_drop 15 (h.recordConditions idx hidx))
  terminalDigest := h.terminalDigest }

theorem DecodedReferenceTranscript.turingIntegerChecks
    {c : Cfg} {words : List Nat} (h : DecodedReferenceTranscript c words) :
    DecodedTuringIntegerChecks c words := {
  perRecord := by
    intro idx hidx
    exact noFailures_take 12 (noFailures_drop 8 (h.recordConditions idx hidx))
  terminalLast := h.terminalLast }

theorem DecodedReferenceTranscript.rosterIntegerChecks
    {c : Cfg} {words : List Nat} (h : DecodedReferenceTranscript c words) :
    DecodedRosterIntegerChecks c words := {
  conjugate := by
    intro idx hidx
    exact noFailures_take 1 (noFailures_drop 20 (h.recordConditions idx hidx))
  firstPointer := by
    intro idx hidx
    exact noFailures_drop 23 (h.recordConditions idx hidx) }

end LeanCompCert.Ports.DirichletLadderExternalSafety
