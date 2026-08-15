import LeanCompCert.Ports.PsiRuntimePrimeLogReadSemantics

/-!
# Conditional store at the end of the compiled psi prime-log body

The last six literal instructions send intermediate-round conversion values
to the dedicated sink cell.  Only the final round writes the proved prime
logarithm into its resident mark-table slot.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayScalarBlock

def psiPrimeLogStoreTargetScalar (sink : Nat) : List Instr :=
  [ .mov 56 (.reg 14)
  , .binop 57 .sub (.lit 1) (.reg 14)
  , .binop 58 .mul (.reg 57) (.lit sink)
  , .binop 59 .mul (.reg 56) (.reg 17)
  , .binop 60 .add (.reg 59) (.reg 58) ]

def psiPrimeLogStoreFlagScalar (sink : Nat) : List Instr :=
  (psiPrimeLogStoreTargetScalar sink).take 2

def psiPrimeLogStoreTermsScalar (sink : Nat) : List Instr :=
  ((psiPrimeLogStoreTargetScalar sink).drop 2).take 2

def psiPrimeLogStoreSumScalar (sink : Nat) : List Instr :=
  (psiPrimeLogStoreTargetScalar sink).drop 4

theorem psiPrimeLogStoreTargetScalar_eq_stages (sink : Nat) :
    psiPrimeLogStoreTargetScalar sink =
      psiPrimeLogStoreFlagScalar sink ++ psiPrimeLogStoreTermsScalar sink ++
        psiPrimeLogStoreSumScalar sink := by rfl

def psiPrimeLogStoreTarget (m : PsiRuntimeMeta) : List AInstr :=
  ((psiPrimeLogBody m).drop 50).take 5

def psiPrimeLogStore (m : PsiRuntimeMeta) : List AInstr :=
  (psiPrimeLogBody m).drop 50

theorem psiPrimeLogStoreTarget_eq_lift (m : PsiRuntimeMeta) :
    psiPrimeLogStoreTarget m =
      lift (psiPrimeLogStoreTargetScalar m.markSink) := by rfl

theorem psiPrimeLogStore_eq_stages (m : PsiRuntimeMeta) :
    psiPrimeLogStore m = psiPrimeLogStoreTarget m ++ [.store 60 55] := by
  rfl

private theorem psiPrimeLogStoreFlagScalar_run
    (sink index : Nat) (s : RegState) (flag : Nat)
    (hflag : s 14 = flag) (hflag01 : flag = 0 ∨ flag = 1) :
    let out := srun index s (psiPrimeLogStoreFlagScalar sink)
    out 56 = flag ∧ out 57 = 1 - flag := by
  have hOneMod : (1 : Nat) % M = 1 := by decide
  have hMsum : 1 + (M - 1) = M := by decide
  rcases hflag01 with rfl | rfl <;>
    simp [psiPrimeLogStoreFlagScalar, psiPrimeLogStoreTargetScalar, srun,
      RegState.set, sdest, sval, denoteOperand, denoteOp, hflag, hOneMod,
      hMsum]

private theorem psiPrimeLogStoreTermsScalar_final_run
    (sink index : Nat) (s : RegState) (target : Nat)
    (h56 : s 56 = 1) (h57 : s 57 = 0) (h17 : s 17 = target)
    (htargetM : target < M) :
    let out := srun index s (psiPrimeLogStoreTermsScalar sink)
    out 58 = 0 ∧ out 59 = target := by
  simp [psiPrimeLogStoreTermsScalar, psiPrimeLogStoreTargetScalar, srun,
    RegState.set, sdest, sval, denoteOperand, denoteOp, h56, h57, h17,
    Nat.mod_eq_of_lt htargetM]

private theorem psiPrimeLogStoreTermsScalar_nonfinal_run
    (sink index : Nat) (s : RegState)
    (h56 : s 56 = 0) (h57 : s 57 = 1) (hsinkM : sink < M) :
    let out := srun index s (psiPrimeLogStoreTermsScalar sink)
    out 58 = sink ∧ out 59 = 0 := by
  simp [psiPrimeLogStoreTermsScalar, psiPrimeLogStoreTargetScalar, srun,
    RegState.set, sdest, sval, denoteOperand, denoteOp, h56, h57,
    Nat.mod_eq_of_lt hsinkM]

private theorem psiPrimeLogStoreSumScalar_run
    (sink index : Nat) (s : RegState) (target : Nat)
    (h58 : s 58 = 0) (h59 : s 59 = target) (htargetM : target < M) :
    (srun index s (psiPrimeLogStoreSumScalar sink)) 60 = target := by
  simp [psiPrimeLogStoreSumScalar, psiPrimeLogStoreTargetScalar, srun,
    RegState.set, sdest, sval, denoteOperand, denoteOp, h58, h59,
    Nat.mod_eq_of_lt htargetM]

private theorem psiPrimeLogStoreSumScalar_rev_run
    (sink index : Nat) (s : RegState) (target : Nat)
    (h58 : s 58 = target) (h59 : s 59 = 0) (htargetM : target < M) :
    (srun index s (psiPrimeLogStoreSumScalar sink)) 60 = target := by
  simp [psiPrimeLogStoreSumScalar, psiPrimeLogStoreTargetScalar, srun,
    RegState.set, sdest, sval, denoteOperand, denoteOp, h58, h59,
    Nat.mod_eq_of_lt htargetM]

private theorem psiPrimeLogStoreTarget_final_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState) (target : Nat)
    (hfinal : s.regs 14 = 1) (htarget : s.regs 17 = target)
    (htargetM : target < M) :
    (arun index s (psiPrimeLogStoreTarget m)).regs 60 = target := by
  let flagged := srun index s.regs (psiPrimeLogStoreFlagScalar m.markSink)
  have hf := psiPrimeLogStoreFlagScalar_run m.markSink index s.regs 1
    hfinal (Or.inr rfl)
  have hf17 : flagged 17 = target :=
    (LeanCompCert.Verified.RegFrame.srun_frame index 17
      (psiPrimeLogStoreFlagScalar m.markSink) (by rfl) s.regs).trans htarget
  let terms := srun index flagged (psiPrimeLogStoreTermsScalar m.markSink)
  have ht := psiPrimeLogStoreTermsScalar_final_run m.markSink index flagged
    target hf.1 hf.2 hf17 htargetM
  have hs := psiPrimeLogStoreSumScalar_run m.markSink index terms target
    ht.1 ht.2 htargetM
  rw [psiPrimeLogStoreTarget_eq_lift, arun_lift,
    psiPrimeLogStoreTargetScalar_eq_stages, srun_append, srun_append]
  exact hs

private theorem psiPrimeLogStoreTarget_nonfinal_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState)
    (hfinal : s.regs 14 = 0) (hsinkM : m.markSink < M) :
    (arun index s (psiPrimeLogStoreTarget m)).regs 60 = m.markSink := by
  let flagged := srun index s.regs (psiPrimeLogStoreFlagScalar m.markSink)
  have hf := psiPrimeLogStoreFlagScalar_run m.markSink index s.regs 0
    hfinal (Or.inl rfl)
  let terms := srun index flagged (psiPrimeLogStoreTermsScalar m.markSink)
  have ht := psiPrimeLogStoreTermsScalar_nonfinal_run m.markSink index flagged
    hf.1 hf.2 hsinkM
  have hs := psiPrimeLogStoreSumScalar_rev_run m.markSink index terms m.markSink
    ht.1 ht.2 hsinkM
  rw [psiPrimeLogStoreTarget_eq_lift, arun_lift,
    psiPrimeLogStoreTargetScalar_eq_stages, srun_append, srun_append]
  exact hs

/-- A final round writes the computed weight to its resident table cell. -/
theorem psiPrimeLogStore_final_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState)
    (target weight : Nat)
    (hfinal : s.regs 14 = 1) (htarget : s.regs 17 = target)
    (hweight : s.regs 55 = weight) (htargetM : target < M) :
    let out := arun index s (psiPrimeLogStore m)
    out.arr = fun x => if x = target then weight else s.arr x := by
  let mid := arun index s (psiPrimeLogStoreTarget m)
  have hm60 := psiPrimeLogStoreTarget_final_run m index s target
    hfinal htarget htargetM
  have hm60' : mid.regs 60 = target := by simpa only [mid] using hm60
  have hm55 : mid.regs 55 = weight := by
    calc
      mid.regs 55 = s.regs 55 :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame index 55
          (psiPrimeLogStoreTarget m) (by rfl) s
      _ = weight := hweight
  have hmarr : mid.arr = s.arr := by
    dsimp only [mid]
    rw [psiPrimeLogStoreTarget_eq_lift, arun_lift]
  rw [psiPrimeLogStore_eq_stages, arun_append]
  change (mid.writeArr (mid.regs 60) (mid.regs 55)).arr = _
  funext x
  simp [AState.writeArr, hm60', hm55, hmarr]

/-- A non-final round writes only to the dedicated sink cell. -/
theorem psiPrimeLogStore_nonfinal_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState) (weight : Nat)
    (hfinal : s.regs 14 = 0) (hweight : s.regs 55 = weight)
    (hsinkM : m.markSink < M) :
    let out := arun index s (psiPrimeLogStore m)
    out.arr = fun x => if x = m.markSink then weight else s.arr x := by
  let mid := arun index s (psiPrimeLogStoreTarget m)
  have hm60 := psiPrimeLogStoreTarget_nonfinal_run m index s hfinal hsinkM
  have hm60' : mid.regs 60 = m.markSink := by simpa only [mid] using hm60
  have hm55 : mid.regs 55 = weight := by
    calc
      mid.regs 55 = s.regs 55 :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame index 55
          (psiPrimeLogStoreTarget m) (by rfl) s
      _ = weight := hweight
  have hmarr : mid.arr = s.arr := by
    dsimp only [mid]
    rw [psiPrimeLogStoreTarget_eq_lift, arun_lift]
  rw [psiPrimeLogStore_eq_stages, arun_append]
  change (mid.writeArr (mid.regs 60) (mid.regs 55)).arr = _
  funext x
  simp [AState.writeArr, hm60', hm55, hmarr]

#print axioms psiPrimeLogStore_final_run
#print axioms psiPrimeLogStore_nonfinal_run

end LeanCompCert.Ports.PsiSegSieve
