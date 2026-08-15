import LeanCompCert.Ports.PsiRuntimePrimeLogFinishSemantics
import LeanCompCert.Verified.BlockDefined

/-!
# Reset/preserve control before a compiled psi fixed-log round

The eight scalar instructions immediately before the fixed-log round either
install the normalized resident prime and clear the accumulator, or preserve
the preceding recurrence state.  The proofs are symbolic in the prime and
round number.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.LogFixed

def psiPrimeLogInitScalar : List Instr :=
  [ .binop 19 .sub (.lit 62) (.reg 18)
  , .binop 20 .band (.reg 19) (.lit 63)
  , .binop 21 .shl (.reg 16) (.reg 20)
  , .binop 22 .sub (.lit 1) (.reg 12)
  , .binop 23 .mul (.reg 12) (.reg 21)
  , .binop 24 .mul (.reg 22) (.reg primeXm)
  , .binop primeXm .add (.reg 23) (.reg 24)
  , .binop primeAa .mul (.reg primeAa) (.reg 22) ]

def psiPrimeLogNormalizeScalar : List Instr :=
  psiPrimeLogInitScalar.take 3

def psiPrimeLogGateScalar : List Instr :=
  (psiPrimeLogInitScalar.drop 3).take 1

def psiPrimeLogSelectScalar : List Instr :=
  psiPrimeLogInitScalar.drop 4

def psiPrimeLogInit (m : PsiRuntimeMeta) : List AInstr :=
  ((psiPrimeLogBody m).drop 9).take 8

def psiPrimeLogCore (m : PsiRuntimeMeta) : List AInstr :=
  ((psiPrimeLogBody m).drop 9).take 28

theorem psiPrimeLogInit_eq_lift (m : PsiRuntimeMeta) :
    psiPrimeLogInit m = lift psiPrimeLogInitScalar := by rfl

theorem psiPrimeLogCore_eq_stages (m : PsiRuntimeMeta) :
    psiPrimeLogCore m = psiPrimeLogInit m ++ psiPrimeLogRound m := by rfl

theorem psiPrimeLogInitScalar_eq_stages :
    psiPrimeLogInitScalar =
      psiPrimeLogNormalizeScalar ++ psiPrimeLogGateScalar ++
        psiPrimeLogSelectScalar := by rfl

private theorem psiPrimeLogShift_facts (e : Nat) (he62 : e ≤ 62) :
    (62 + (M - e)) % M = 62 - e ∧
      (62 - e) &&& 63 = 62 - e ∧ 62 - e < M := by
  have hsub : (62 + (M - e)) % M = 62 - e := by
    have hs := LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le
      (a := 62) (b := e) he62 (by decide)
    exact Option.some.inj hs
  have hshift : (62 - e) &&& 63 = 62 - e := by
    have hlt : 62 - e < 64 := by omega
    change (62 - e) &&& (2 ^ 6 - 1) = 62 - e
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
  exact ⟨hsub, hshift, Nat.lt_trans (show 62 - e < 64 by omega) (by decide)⟩

private theorem psiPrimeLogNormalizeScalar_run
    (index : Nat) (s : RegState) (n e : Nat)
    (hn : s 16 = n) (he : s 18 = e)
    (he62 : e ≤ 62) (hnorm : n <<< (62 - e) < M) :
    (srun index s psiPrimeLogNormalizeScalar) 21 = n <<< (62 - e) := by
  obtain ⟨hsub, hshift, hshiftM⟩ := psiPrimeLogShift_facts e he62
  have hmask : (63 : Nat) % M = 63 := by decide
  simp [psiPrimeLogNormalizeScalar, psiPrimeLogInitScalar, srun,
    RegState.set, sdest, sval, denoteOperand, denoteOp, hn, he, hsub,
    hmask, hshift, Nat.mod_eq_of_lt hshiftM, Nat.mod_eq_of_lt hnorm]

private theorem psiPrimeLogGateScalar_start_run
    (index : Nat) (s : RegState) (hstart : s 12 = 1) :
    (srun index s psiPrimeLogGateScalar) 22 = 0 := by
  have hMsum : 1 + (M - 1) = M := by decide
  simp [psiPrimeLogGateScalar, psiPrimeLogInitScalar, srun, RegState.set,
    sdest, sval, denoteOperand, denoteOp, hstart, hMsum]

private theorem psiPrimeLogGateScalar_continue_run
    (index : Nat) (s : RegState) (hstart : s 12 = 0) :
    (srun index s psiPrimeLogGateScalar) 22 = 1 := by
  have hOneM : (1 : Nat) % M = 1 := by decide
  simp [psiPrimeLogGateScalar, psiPrimeLogInitScalar, srun, RegState.set,
    sdest, sval, denoteOperand, denoteOp, hstart, hOneM]

private theorem psiPrimeLogSelectScalar_start_run
    (index : Nat) (s : RegState) (x : Nat)
    (hstart : s 12 = 1) (h21 : s 21 = x) (h22 : s 22 = 0)
    (hxM : x < M) :
    let out := srun index s psiPrimeLogSelectScalar
    out primeXm = x ∧ out primeAa = 0 := by
  simp [psiPrimeLogSelectScalar, psiPrimeLogInitScalar, srun, RegState.set,
    sdest, sval, denoteOperand, denoteOp, hstart, h21, h22,
    Nat.mod_eq_of_lt hxM, primeXm, primeAa]

private theorem psiPrimeLogSelectScalar_continue_run
    (index : Nat) (s : RegState) (normalized x a : Nat)
    (hstart : s 12 = 0) (h21 : s 21 = normalized) (h22 : s 22 = 1)
    (hx : s primeXm = x) (ha : s primeAa = a)
    (_hnormM : normalized < M) (hxM : x < M) (haM : a < M) :
    let out := srun index s psiPrimeLogSelectScalar
    out primeXm = x ∧ out primeAa = a := by
  have hx' : s 362 = x := by simpa only [primeXm] using hx
  have ha' : s 363 = a := by simpa only [primeAa] using ha
  simp [psiPrimeLogSelectScalar, psiPrimeLogInitScalar, srun, RegState.set,
    sdest, sval, denoteOperand, denoteOp, hstart, h21, h22, hx', ha',
    Nat.mod_eq_of_lt hxM, Nat.mod_eq_of_lt haM, primeXm, primeAa]

/-- A first round installs the normalized prime and clears the accumulator. -/
theorem psiPrimeLogInitScalar_start_run
    (index : Nat) (s : RegState) (n e : Nat)
    (hstart : s 12 = 1) (hn : s 16 = n) (he : s 18 = e)
    (he62 : e ≤ 62) (hnorm : n <<< (62 - e) < M) :
    let out := srun index s psiPrimeLogInitScalar
    out primeXm = n <<< (62 - e) ∧ out primeAa = 0 := by
  let normalized := srun index s psiPrimeLogNormalizeScalar
  have h21 := psiPrimeLogNormalizeScalar_run index s n e hn he he62 hnorm
  have h12 : normalized 12 = 1 :=
    (LeanCompCert.Verified.RegFrame.srun_frame index 12
      psiPrimeLogNormalizeScalar (by rfl) s).trans hstart
  let gated := srun index normalized psiPrimeLogGateScalar
  have h22 := psiPrimeLogGateScalar_start_run index normalized h12
  have gated12 : gated 12 = 1 :=
    (LeanCompCert.Verified.RegFrame.srun_frame index 12
      psiPrimeLogGateScalar (by rfl) normalized).trans h12
  have gated21 : gated 21 = n <<< (62 - e) :=
    (LeanCompCert.Verified.RegFrame.srun_frame index 21
      psiPrimeLogGateScalar (by rfl) normalized).trans h21
  have hout := psiPrimeLogSelectScalar_start_run index gated
    (n <<< (62 - e)) gated12 gated21 h22 hnorm
  rw [psiPrimeLogInitScalar_eq_stages, srun_append, srun_append]
  exact hout

/-- A continuation round preserves the recurrence registers. -/
theorem psiPrimeLogInitScalar_continue_run
    (index : Nat) (s : RegState) (n e x a : Nat)
    (hstart : s 12 = 0) (hn : s 16 = n) (he : s 18 = e)
    (hx : s primeXm = x) (ha : s primeAa = a)
    (he62 : e ≤ 62) (hnorm : n <<< (62 - e) < M)
    (hxM : x < M) (haM : a < M) :
    let out := srun index s psiPrimeLogInitScalar
    out primeXm = x ∧ out primeAa = a := by
  let normalized := srun index s psiPrimeLogNormalizeScalar
  have h21 := psiPrimeLogNormalizeScalar_run index s n e hn he he62 hnorm
  have h12 : normalized 12 = 0 :=
    (LeanCompCert.Verified.RegFrame.srun_frame index 12
      psiPrimeLogNormalizeScalar (by rfl) s).trans hstart
  have hxm : normalized primeXm = x :=
    (LeanCompCert.Verified.RegFrame.srun_frame index primeXm
      psiPrimeLogNormalizeScalar (by rfl) s).trans hx
  have haa : normalized primeAa = a :=
    (LeanCompCert.Verified.RegFrame.srun_frame index primeAa
      psiPrimeLogNormalizeScalar (by rfl) s).trans ha
  let gated := srun index normalized psiPrimeLogGateScalar
  have h22 := psiPrimeLogGateScalar_continue_run index normalized h12
  have gated12 : gated 12 = 0 :=
    (LeanCompCert.Verified.RegFrame.srun_frame index 12
      psiPrimeLogGateScalar (by rfl) normalized).trans h12
  have gated21 : gated 21 = n <<< (62 - e) :=
    (LeanCompCert.Verified.RegFrame.srun_frame index 21
      psiPrimeLogGateScalar (by rfl) normalized).trans h21
  have gatedXm : gated primeXm = x :=
    (LeanCompCert.Verified.RegFrame.srun_frame index primeXm
      psiPrimeLogGateScalar (by rfl) normalized).trans hxm
  have gatedAa : gated primeAa = a :=
    (LeanCompCert.Verified.RegFrame.srun_frame index primeAa
      psiPrimeLogGateScalar (by rfl) normalized).trans haa
  have hout := psiPrimeLogSelectScalar_continue_run index gated
    (n <<< (62 - e)) x a gated12 gated21 h22 gatedXm gatedAa
    hnorm hxM haM
  rw [psiPrimeLogInitScalar_eq_stages, srun_append, srun_append]
  exact hout

theorem psiPrimeLogInit_start_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState) (n e : Nat)
    (hstart : s.regs 12 = 1) (hn : s.regs 16 = n) (he : s.regs 18 = e)
    (he62 : e ≤ 62) (hnorm : n <<< (62 - e) < M) :
    let out := arun index s (psiPrimeLogInit m)
    out.regs primeXm = n <<< (62 - e) ∧ out.regs primeAa = 0 ∧
      out.arr = s.arr := by
  rw [psiPrimeLogInit_eq_lift, arun_lift]
  have h := psiPrimeLogInitScalar_start_run index s.regs n e
    hstart hn he he62 hnorm
  exact ⟨h.1, h.2, rfl⟩

theorem psiPrimeLogInit_continue_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState) (n e x a : Nat)
    (hstart : s.regs 12 = 0) (hn : s.regs 16 = n) (he : s.regs 18 = e)
    (hx : s.regs primeXm = x) (ha : s.regs primeAa = a)
    (he62 : e ≤ 62) (hnorm : n <<< (62 - e) < M)
    (hxM : x < M) (haM : a < M) :
    let out := arun index s (psiPrimeLogInit m)
    out.regs primeXm = x ∧ out.regs primeAa = a ∧ out.arr = s.arr := by
  rw [psiPrimeLogInit_eq_lift, arun_lift]
  have h := psiPrimeLogInitScalar_continue_run index s.regs n e x a
    hstart hn he hx ha he62 hnorm hxM haM
  exact ⟨h.1, h.2, rfl⟩

#print axioms psiPrimeLogInitScalar_start_run
#print axioms psiPrimeLogInitScalar_continue_run
#print axioms psiPrimeLogInit_start_run
#print axioms psiPrimeLogInit_continue_run

end LeanCompCert.Ports.PsiSegSieve
