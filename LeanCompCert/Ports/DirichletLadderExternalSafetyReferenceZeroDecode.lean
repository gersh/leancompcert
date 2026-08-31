import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditions

/-! Decode a zero independent reference counter into its per-record and
terminal source propositions.  This is list-fold reasoning only; it evaluates
no transcript. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert.Ports.DirichletLadder

/-- Reference state after exactly `n` decoded records. -/
def referenceStateAt (c : Cfg) (words : List Nat) (n : Nat) : RefState :=
  (List.range n).foldl (refStep c words) refInit

theorem referenceStateAt_zero (c : Cfg) (words : List Nat) :
    referenceStateAt c words 0 = refInit := by rfl

theorem referenceStateAt_succ (c : Cfg) (words : List Nat) (n : Nat) :
    referenceStateAt c words (n + 1) =
      refStep c words (referenceStateAt c words n) n := by
  simp only [referenceStateAt, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem refStep_viol_mono (c : Cfg) (words : List Nat)
    (st : RefState) (idx : Nat) :
    st.viol ≤ (refStep c words st idx).viol := by
  rw [refStep_viol_eq_referenceConditions]
  exact bumps_ge _ _

theorem referenceStateAt_viol_mono_succ
    (c : Cfg) (words : List Nat) (n : Nat) :
    (referenceStateAt c words n).viol ≤
      (referenceStateAt c words (n + 1)).viol := by
  rw [referenceStateAt_succ]
  exact refStep_viol_mono c words _ n

theorem referenceStateAt_viol_mono
    (c : Cfg) (words : List Nat) (m n : Nat) (hmn : m ≤ n) :
    (referenceStateAt c words m).viol ≤
      (referenceStateAt c words n).viol := by
  induction n with
  | zero =>
      have : m = 0 := by omega
      subst m
      exact Nat.le_refl _
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m
        exact Nat.le_refl _
      · exact Nat.le_trans (ih (by omega))
          (referenceStateAt_viol_mono_succ c words n)

/-- Fully decoded integer transcript proposition.  The state in each record
condition is exactly the state obtained from the preceding reference prefix. -/
structure DecodedReferenceTranscript (c : Cfg) (words : List Nat) : Prop where
  recordConditions : ∀ idx, idx < c.records →
    NoFailures (referenceConditions c words (referenceStateAt c words idx) idx)
  terminalLast : (referenceStateAt c words c.records).prevLast = 1
  terminalDigest : (referenceStateAt c words c.records).prevDig = c.termDigest

theorem reference_final_viol_zero_of_refViolations_zero
    (c : Cfg) (words : List Nat)
    (hzero : refViolations c words = 0) :
    (referenceStateAt c words c.records).viol = 0 := by
  let st := referenceStateAt c words c.records
  have hge1 : st.viol ≤ bump (st.prevLast != 1) st.viol := by
    cases (st.prevLast != 1) <;> simp [bump]
  have hge2 : bump (st.prevLast != 1) st.viol ≤
      bump (st.prevDig != c.termDigest) (bump (st.prevLast != 1) st.viol) := by
    cases (st.prevDig != c.termDigest) <;> simp [bump]
  change bump (st.prevDig != c.termDigest)
    (bump (st.prevLast != 1) st.viol) = 0 at hzero
  change st.viol = 0
  omega

theorem reference_prefix_viol_zero_of_refViolations_zero
    (c : Cfg) (words : List Nat)
    (hzero : refViolations c words = 0)
    (n : Nat) (hn : n ≤ c.records) :
    (referenceStateAt c words n).viol = 0 := by
  have hmono := referenceStateAt_viol_mono c words n c.records hn
  have hfinal := reference_final_viol_zero_of_refViolations_zero c words hzero
  omega

theorem reference_recordConditions_of_refViolations_zero
    (c : Cfg) (words : List Nat)
    (hzero : refViolations c words = 0)
    (idx : Nat) (hidx : idx < c.records) :
    NoFailures
      (referenceConditions c words (referenceStateAt c words idx) idx) := by
  have hbefore := reference_prefix_viol_zero_of_refViolations_zero c words
    hzero idx (by omega)
  have hafter := reference_prefix_viol_zero_of_refViolations_zero c words
    hzero (idx + 1) (by omega)
  rw [referenceStateAt_succ, refStep_viol_eq_referenceConditions] at hafter
  rw [hbefore] at hafter
  exact noFailures_of_bumps_zero _ hafter

theorem reference_terminalLast_of_refViolations_zero
    (c : Cfg) (words : List Nat)
    (hzero : refViolations c words = 0) :
    (referenceStateAt c words c.records).prevLast = 1 := by
  let st := referenceStateAt c words c.records
  change bump (st.prevDig != c.termDigest)
    (bump (st.prevLast != 1) st.viol) = 0 at hzero
  by_cases hlast : st.prevLast = 1
  · exact hlast
  · have hb : (st.prevLast != 1) = true := by
      simp [bne_iff_ne, hlast]
    rw [hb] at hzero
    cases hd : (st.prevDig != c.termDigest) <;> simp [hd, bump] at hzero

theorem reference_terminalDigest_of_refViolations_zero
    (c : Cfg) (words : List Nat)
    (hzero : refViolations c words = 0) :
    (referenceStateAt c words c.records).prevDig = c.termDigest := by
  let st := referenceStateAt c words c.records
  change bump (st.prevDig != c.termDigest)
    (bump (st.prevLast != 1) st.viol) = 0 at hzero
  by_cases hdig : st.prevDig = c.termDigest
  · exact hdig
  · have hb : (st.prevDig != c.termDigest) = true := by
      simp [bne_iff_ne, hdig]
    rw [hb] at hzero
    simp [bump] at hzero

/-- Zero reference violations is a lossless certificate of all integer-level
record and terminal checks. -/
theorem decodedReferenceTranscript_of_refViolations_zero
    (c : Cfg) (words : List Nat)
    (hzero : refViolations c words = 0) :
    DecodedReferenceTranscript c words := {
  recordConditions := reference_recordConditions_of_refViolations_zero c words
    hzero
  terminalLast := reference_terminalLast_of_refViolations_zero c words hzero
  terminalDigest := reference_terminalDigest_of_refViolations_zero c words hzero }

end LeanCompCert.Ports.DirichletLadderExternalSafety
