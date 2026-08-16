import LeanCompCert.Ports.RS62Loop410Program
import LeanCompCert.Ports.ArraySegMobiusSignal
import LeanCompCert.Verified.MulWide
import LeanCompCert.Verified.ArrayRegFrame
import LeanCompCert.Verified.SqrtEquiv

/-!
# Source semantics of the compiled RS62 (4.10) consumer

The production fold is kept symbolic throughout this file.  Sticky zero
verdicts turn the machine's modular additions into ordinary natural-number
updates; the half-limb multiplier theorem identifies both strict-guard
products exactly.
-/

namespace LeanCompCert.Ports.RS62Loop410Sound

set_option maxRecDepth 10000

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports
open RS62Loop410Program

structure State410 where
  logL : Nat
  logU : Nat
  product : Nat
  sqrt : Nat
  bad : Nat
  deriving Repr, DecidableEq

def ceilRootOf (n s : Nat) : Nat := s + if s * s < n then 1 else 0

def rootTerm (n s : Nat) : Nat := RS62.fpD / ceilRootOf n s

def productCandidate (gate n P : Nat) : Nat :=
  P + gate * ((P + n - 2) / (n - 1))

def guardStrong (n logL P s : Nat) : Prop :=
  P * 10000000 < 17810724 * (logL + 2 * rootTerm n s)

def sqrtNext (n s : Nat) : Nat :=
  s + if (s + 1) * (s + 1) ≤ n + 1 then 1 else 0

def sourceStep (arr : Nat → Nat) (n0 : Nat)
    (st : State410) (k : Nat) : State410 :=
  let n := n0 + k
  let gate := arr k
  let P' := productCandidate gate n st.product
  { logL := st.logL + RS62.incLWord n
    logU := st.logU + RS62.incUWord n
    product := P'
    sqrt := sqrtNext n st.sqrt
    bad := st.bad ||| gate *
      (if P' * 10000000 <
          17810724 * (st.logL + 2 * rootTerm n st.sqrt) then 0 else 1) }

def sourceFold (arr : Nat → Nat) (n0 f : Nat) (initial : State410) :
    State410 :=
  (List.range f).foldl (sourceStep arr n0) initial

theorem sourceFold_succ (arr : Nat → Nat) (n0 f : Nat)
    (initial : State410) :
    sourceFold arr n0 (f + 1) initial =
      sourceStep arr n0 (sourceFold arr n0 f initial) f := by
  unfold sourceFold
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem snapshotBody_run (k : Nat) (s : AState) :
    let out := arun k s snapshotBody
    out.regs rOldL = s.regs rLogL ∧
      out.regs rBad = s.regs rBad ∧ out.arr = s.arr := by
  simp [snapshotBody, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, rOldL, rLogL, rBad]

theorem logBadBody_run (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) :
    let out := arun k s logBadBody
    out.regs rBad =
      (s.regs rBad ||| s.regs RS62PrimeMaskLadderOverflow.rBad) ∧
      out.arr = s.arr := by
  rw [logBadBody, arun_lift]
  change ((s.regs rBad |||
    s.regs RS62PrimeMaskLadderOverflow.rBad) % M = _) ∧ _
  rw [Nat.mod_eq_of_lt (Section413G1Denote.lor_lt_M
    (hword rBad) (hword RS62PrimeMaskLadderOverflow.rBad))]
  exact ⟨rfl, rfl⟩

private theorem bor_eq_zero_left {a b : Nat} (h : a ||| b = 0) : a = 0 := by
  have hle : a ≤ a ||| b := Nat.left_le_or
  omega

private theorem bor_eq_zero_right {a b : Nat} (h : a ||| b = 0) : b = 0 := by
  rw [Nat.or_comm] at h
  exact bor_eq_zero_left h

private theorem aframe (k r : Nat) (l : List AInstr) (s : AState)
    (h : ArrayRegFrame.writes r l = false) :
    (arun k s l).regs r = s.regs r :=
  ArrayRegFrame.arun_frame k r l h s

private theorem no_wrap_of_not_lt_left {a d : Nat}
    (ha : a < M) (hd : d < M) (h : ¬ (a + d) % M < a) :
    a + d < M := by
  apply Nat.lt_of_not_ge
  intro hM
  have hsum : a + d < M + M := by omega
  apply h
  rw [Nat.mod_eq_sub_mod hM, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem add_base_sub_mod (n base d : Nat)
    (hd : d ≤ n) (hn : n < base) :
    (n + base - d) % base = n - d := by
  rw [Nat.sub_add_comm hd, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem wrapCheckBody_run (k new old : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) :
    let out := arun k s (wrapCheckBody new old)
    out.regs rBad =
      (s.regs rBad ||| (if s.regs new < s.regs old then 1 else 0)) ∧
      out.arr = s.arr := by
  rw [wrapCheckBody, arun_lift]
  simp only [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    Option.getD_some, rWrap, rBad, M, Nat.reduceEqDiff, if_true, if_false]
  by_cases h : s.regs new < s.regs old
  · simp only [h, if_true]
    constructor
    · apply Nat.mod_eq_of_lt
      simpa only [rBad, M] using
        (Section413G1Denote.lor_lt_M (hword rBad) (by decide : 1 < M))
    · trivial
  · simp only [h, if_false, Nat.or_zero]
    constructor
    · apply Nat.mod_eq_of_lt
      simpa only [rBad, M] using hword rBad
    · trivial

theorem productNumerAddBody_run (k : Nat) (s : AState) :
    let out := arun k s productNumerAddBody
    out.regs rQ = (s.regs rP + s.regs rNm2) % M ∧
      out.regs rP = s.regs rP ∧ out.regs rBad = s.regs rBad ∧
      out.arr = s.arr := by
  rw [productNumerAddBody, arun_lift]
  simp [srun, sdest, sval, denoteOperand,
    denoteOp, RegState.set, rQ, rP, rNm2, rN, rBad]

theorem productNumerBody_zero_sound (k : Nat) (s : AState)
    (hP : s.regs rP < M) (hnm2 : s.regs rNm2 < M)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hzero : (arun k s productNumerBody).regs rBad = 0) :
    s.regs rBad = 0 ∧ s.regs rP + s.regs rNm2 < M ∧
      (arun k s productNumerBody).regs rQ = s.regs rP + s.regs rNm2 ∧
      (arun k s productNumerBody).arr = s.arr := by
  let a := arun k s productNumerAddBody
  let out := arun k a productNumerCheckBody
  let q := (s.regs rP + s.regs rNm2) % M
  have hqM : q < M := Nat.mod_lt _ M_pos
  have ha := productNumerAddBody_run k s
  change a.regs rQ = q ∧ a.regs rP = s.regs rP ∧
    a.regs rBad = s.regs rBad ∧ a.arr = s.arr at ha
  have haword : ∀ j, a.regs j < M :=
    arun_regs_word k productNumerAddBody s hword harr
  have hc := wrapCheckBody_run k rQ rP a haword
  change out.regs rBad =
      (a.regs rBad ||| (if a.regs rQ < a.regs rP then 1 else 0)) ∧
    out.arr = a.arr at hc
  have hout : arun k s productNumerBody = out := by
    simp only [productNumerBody, arun_append, a, out, productNumerCheckBody]
  have houtQ : out.regs rQ = a.regs rQ :=
    ArrayRegFrame.arun_frame k rQ productNumerCheckBody (by rfl) a
  have houtZero : out.regs rBad = 0 := by rw [← hout]; exact hzero
  have hz : s.regs rBad ||| (if q < s.regs rP then 1 else 0) = 0 := by
    rw [← ha.2.2.1, ← ha.1, ← ha.2.1, ← hc.1]
    exact houtZero
  have hnot : ¬ q < s.regs rP := by
    intro h
    have := bor_eq_zero_right hz
    simp [h] at this
  have hsum := no_wrap_of_not_lt_left hP hnm2 hnot
  exact ⟨bor_eq_zero_left hz, hsum,
    hout.symm ▸ houtQ.trans (ha.1.trans (Nat.mod_eq_of_lt hsum)),
    hout.symm ▸ hc.2.trans ha.2.2.2⟩

theorem productDivBody_run (k : Nat) (s : AState)
    (hden : s.regs 237 ≠ 0) (hQ : s.regs rQ < M) :
    let out := arun k s productDivBody
    out.regs rQ = s.regs rQ / s.regs 237 ∧
      out.arr = s.arr := by
  rw [productDivBody, arun_lift]
  simp only [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    Option.getD_some, rQ, M, Nat.reduceEqDiff, if_true, if_false]
  rw [if_neg hden]
  exact ⟨Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
    hQ), trivial⟩

theorem productCommitBody_zero_sound (k : Nat) (s : AState)
    (hP : s.regs rP < M) (hGate : s.regs rGate ≤ 1)
    (hQ : s.regs rQ < M)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hzero : (arun k s productCommitBody).regs rBad = 0) :
    s.regs rBad = 0 ∧ s.regs rP + s.regs rGate * s.regs rQ < M ∧
      (arun k s productCommitBody).regs rPNext =
        s.regs rP + s.regs rGate * s.regs rQ ∧
      (arun k s productCommitBody).arr = s.arr := by
  have hmul : s.regs rGate * s.regs rQ < M := by
    rcases (by omega : s.regs rGate = 0 ∨ s.regs rGate = 1) with h | h <;>
      simp [h, hQ, M_pos]
  let m := arun k s productCommitMulBody
  let a := arun k m productCommitAddBody
  let out := arun k a productCommitCheckBody
  let q := (s.regs rP + s.regs rGate * s.regs rQ) % M
  have hmulmod :
      (s.regs RS62PrimeMaskLadder.rGate * s.regs 212) % M =
        s.regs RS62PrimeMaskLadder.rGate * s.regs 212 := by
    apply Nat.mod_eq_of_lt
    simpa only [rGate, rQ] using hmul
  have hm : m.regs rPNext = s.regs rGate * s.regs rQ ∧
      m.regs rP = s.regs rP ∧ m.regs rBad = s.regs rBad ∧
      m.arr = s.arr := by
    dsimp only [m]
    rw [productCommitMulBody, arun_lift]
    simp [srun, sdest, sval,
      denoteOperand, denoteOp, RegState.set, rPNext, rGate, rQ, rP, rBad,
      hmulmod]
  have ha : a.regs rPNext = q ∧ a.regs rP = s.regs rP ∧
      a.regs rBad = s.regs rBad ∧ a.arr = s.arr := by
    dsimp only [a]
    rw [productCommitAddBody, arun_lift]
    simp only [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, rPNext, rP, rBad, M, Nat.reduceEqDiff,
      if_true, if_false]
    have hmP : m.regs 211 = s.regs 211 := by simpa only [rP] using hm.2.1
    have hmPN : m.regs 213 = s.regs rGate * s.regs rQ := by
      simpa only [rPNext] using hm.1
    exact ⟨by rw [hmP, hmPN]; rfl, hmP, by simpa only [rBad] using hm.2.2.1,
      hm.2.2.2⟩
  have hmword : ∀ j, m.regs j < M :=
    arun_regs_word k productCommitMulBody s hword harr
  have hmarr : ∀ j, m.arr j < M :=
    arun_arr_word k productCommitMulBody s hword harr
  have haword : ∀ j, a.regs j < M :=
    arun_regs_word k productCommitAddBody m hmword hmarr
  have hc := wrapCheckBody_run k rPNext rP a haword
  change out.regs rBad =
      (a.regs rBad ||| (if a.regs rPNext < a.regs rP then 1 else 0)) ∧
    out.arr = a.arr at hc
  have hout : arun k s productCommitBody = out := by
    simp only [productCommitBody, arun_append, m, a, out,
      productCommitCheckBody]
  have houtP : out.regs rPNext = a.regs rPNext :=
    ArrayRegFrame.arun_frame k rPNext productCommitCheckBody (by rfl) a
  have houtZero : out.regs rBad = 0 := by rw [← hout]; exact hzero
  have hz : s.regs rBad ||| (if q < s.regs rP then 1 else 0) = 0 := by
    rw [← ha.2.2.1, ← ha.1, ← ha.2.1, ← hc.1]
    exact houtZero
  have hnot : ¬ q < s.regs rP := by
    intro h
    have := bor_eq_zero_right hz
    simp [h] at this
  have hsum := no_wrap_of_not_lt_left hP hmul hnot
  exact ⟨bor_eq_zero_left hz, hsum,
    hout.symm ▸ houtP.trans (ha.1.trans (Nat.mod_eq_of_lt hsum)),
    hout.symm ▸ hc.2.trans ha.2.2.2⟩

theorem productBody_zero_sound (k : Nat) (s : AState)
    (hP : s.regs rP < M) (hnm2 : s.regs rNm2 < M)
    (hGate : s.regs rGate ≤ 1) (hden : s.regs 237 ≠ 0)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hzero : (arun k s productBody).regs rBad = 0) :
    let q := (s.regs rP + s.regs rNm2) / s.regs 237
    s.regs rBad = 0 ∧ s.regs rP + s.regs rNm2 < M ∧
      s.regs rP + s.regs rGate * q < M ∧
      (arun k s productBody).regs rPNext =
        s.regs rP + s.regs rGate * q ∧
      (arun k s productBody).arr = s.arr := by
  dsimp only
  let n := arun k s productNumerBody
  let d := arun k n productDivBody
  let out := arun k d productCommitBody
  have hnword := arun_regs_word k productNumerBody s hword harr
  have hnarr := arun_arr_word k productNumerBody s hword harr
  have hdword := arun_regs_word k productDivBody n hnword hnarr
  have hdarr := arun_arr_word k productDivBody n hnword hnarr
  have hnP : n.regs rP = s.regs rP := aframe k rP _ _ (by rfl)
  have hnDen : n.regs 237 = s.regs 237 := aframe k 237 _ _ (by rfl)
  have hnGate : n.regs rGate = s.regs rGate := aframe k rGate _ _ (by rfl)
  have hdP : d.regs rP = s.regs rP :=
    (aframe k rP productDivBody n (by rfl)).trans hnP
  have hdGate : d.regs rGate = s.regs rGate :=
    (aframe k rGate productDivBody n (by rfl)).trans hnGate
  have hdBad : d.regs rBad = n.regs rBad := aframe k rBad _ _ (by rfl)
  have hout : arun k s productBody = out := by
    simp only [productBody, arun_append, n, d, out]
  have houtZero : out.regs rBad = 0 := by rw [← hout]; exact hzero
  have hc := productCommitBody_zero_sound k d
    (by rw [hdP]; exact hP) (by rw [hdGate]; exact hGate)
    (hdword rQ) hdword hdarr houtZero
  have hnZero : n.regs rBad = 0 := hdBad.symm.trans hc.1
  have hnrun := productNumerBody_zero_sound k s hP hnm2 hword harr hnZero
  have hdRun := productDivBody_run k n (by rw [hnDen]; exact hden)
    (hnword rQ)
  change d.regs rQ = n.regs rQ / n.regs 237 ∧ d.arr = n.arr at hdRun
  have hdQ : d.regs rQ =
      (s.regs rP + s.regs rNm2) / s.regs 237 := by
    rw [hdRun.1, hnrun.2.2.1, hnDen]
  refine ⟨hnrun.1, hnrun.2.1, ?_, ?_, ?_⟩
  · simpa [hdP, hdGate, hdQ] using hc.2.1
  · rw [hout, hc.2.2.1, hdP, hdGate, hdQ]
  · rw [hout, hc.2.2.2, hdRun.2, hnrun.2.2.2]

theorem rootCeilBody_run (k : Nat) (s : AState)
    (hsq : s.regs rSqrt * s.regs rSqrt < M)
    (hs1 : s.regs rSqrt + 1 < M) :
    let out := arun k s rootCeilBody
    out.regs rCeilRoot = ceilRootOf (s.regs rN) (s.regs rSqrt) ∧
      out.regs rBad = s.regs rBad ∧ out.arr = s.arr := by
  rw [rootCeilBody, arun_lift]
  have hsq' : s.regs 214 * s.regs 214 < 2 ^ 64 := by
    simpa only [rSqrt, M] using hsq
  have hs1' : s.regs 214 + 1 < 2 ^ 64 := by
    simpa only [rSqrt, M] using hs1
  have hnr : RS62PrimeMaskLadder.rN ≠ 215 := by decide
  have hsqM : s.regs 214 * s.regs 214 % M =
      s.regs 214 * s.regs 214 := by
    apply Nat.mod_eq_of_lt
    simpa only [rSqrt] using hsq
  simp only [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    Option.getD_some, rSq, rSqrt, rBump, rCeilRoot, rBad,
    Nat.reduceEqDiff, if_true, if_false, hnr, hsqM]
  by_cases h : s.regs 214 * s.regs 214 < s.regs RS62PrimeMaskLadder.rN
  · have hs1M : (s.regs 214 + 1) % M = s.regs 214 + 1 := by
      apply Nat.mod_eq_of_lt
      simpa only [rSqrt] using hs1
    simp [h, ceilRootOf, rSqrt, rN, hs1M]
  · have hsM : s.regs 214 < 2 ^ 64 := by omega
    have hsMM : s.regs 214 % M = s.regs 214 := by
      apply Nat.mod_eq_of_lt
      simpa only [M] using hsM
    simp [h, ceilRootOf, rSqrt, rN, hsMM]

theorem rootDivideBody_run (k : Nat) (s : AState)
    (hc : s.regs rCeilRoot ≠ 0) :
    let out := arun k s rootDivideBody
    out.regs rRootTerm = RS62.fpD / s.regs rCeilRoot ∧
      out.regs rBad = s.regs rBad ∧ out.arr = s.arr := by
  rw [rootDivideBody, arun_lift]
  have hc' : s.regs 217 ≠ 0 := by simpa only [rCeilRoot] using hc
  have hD : RS62.fpD % M = RS62.fpD := Nat.mod_eq_of_lt (by decide)
  have hdiv : RS62.fpD / s.regs 217 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
  have hdivM : (RS62.fpD / s.regs 217) % M =
      RS62.fpD / s.regs 217 := Nat.mod_eq_of_lt (by simpa only [M] using hdiv)
  simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rRootTerm, rCeilRoot, rBad, hc', hD, hdivM]

theorem rootDoubleAddBody_run (k : Nat) (s : AState) :
    let out := arun k s rootDoubleAddBody
    out.regs rRhsBase = (s.regs rRootTerm + s.regs rRootTerm) % M ∧
      out.regs rRootTerm = s.regs rRootTerm ∧
      out.regs rBad = s.regs rBad ∧ out.arr = s.arr := by
  rw [rootDoubleAddBody, arun_lift]
  simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rRhsBase, rRootTerm, rBad]

theorem rootDoubleBody_zero_sound (k : Nat) (s : AState)
    (hc : s.regs rCeilRoot ≠ 0)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hzero : (arun k s rootDoubleBody).regs rBad = 0) :
    let q := RS62.fpD / s.regs rCeilRoot
    s.regs rBad = 0 ∧ 2 * q < M ∧
      (arun k s rootDoubleBody).regs rRhsBase = 2 * q ∧
      (arun k s rootDoubleBody).arr = s.arr := by
  dsimp only
  let d := arun k s rootDivideBody
  let a := arun k d rootDoubleAddBody
  let out := arun k a rootDoubleCheckBody
  have hd := rootDivideBody_run k s hc
  change d.regs rRootTerm = RS62.fpD / s.regs rCeilRoot ∧
    d.regs rBad = s.regs rBad ∧ d.arr = s.arr at hd
  have hdword := arun_regs_word k rootDivideBody s hword harr
  have hdarr := arun_arr_word k rootDivideBody s hword harr
  have ha := rootDoubleAddBody_run k d
  change a.regs rRhsBase = (d.regs rRootTerm + d.regs rRootTerm) % M ∧
    a.regs rRootTerm = d.regs rRootTerm ∧
    a.regs rBad = d.regs rBad ∧ a.arr = d.arr at ha
  have haword := arun_regs_word k rootDoubleAddBody d hdword hdarr
  have hcRun := wrapCheckBody_run k rRhsBase rRootTerm a haword
  change out.regs rBad =
      (a.regs rBad ||| (if a.regs rRhsBase < a.regs rRootTerm then 1 else 0)) ∧
    out.arr = a.arr at hcRun
  have hout : arun k s rootDoubleBody = out := by
    simp only [rootDoubleBody, arun_append, d, a, out,
      rootDoubleCheckBody]
  have houtZero : out.regs rBad = 0 := by rw [← hout]; exact hzero
  have hz := bor_eq_zero_left (hcRun.1.symm.trans houtZero)
  have hflag := bor_eq_zero_right (hcRun.1.symm.trans houtZero)
  have hnot : ¬ a.regs rRhsBase < a.regs rRootTerm := by
    intro h
    simp [h] at hflag
  have hqM : RS62.fpD / s.regs rCeilRoot < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
  have hnot' : ¬ (d.regs rRootTerm + d.regs rRootTerm) % M <
      d.regs rRootTerm := by
    rw [← ha.1, ← ha.2.1]
    exact hnot
  have hadd : RS62.fpD / s.regs rCeilRoot +
      RS62.fpD / s.regs rCeilRoot < M := by
    have hw := no_wrap_of_not_lt_left
      (by rw [hd.1]; exact hqM) (by rw [hd.1]; exact hqM) hnot'
    rwa [hd.1] at hw
  have hsum : 2 * (RS62.fpD / s.regs rCeilRoot) < M := by omega
  have houtR : out.regs rRhsBase = a.regs rRhsBase :=
    aframe k rRhsBase rootDoubleCheckBody a (by rfl)
  refine ⟨?_, hsum, ?_, ?_⟩
  · rw [← hd.2.1, ← ha.2.2.1]
    exact hz
  · rw [hout, houtR, ha.1, hd.1, Nat.mod_eq_of_lt hadd]
    omega
  · rw [hout, hcRun.2, ha.2.2.2, hd.2.2]

theorem rootBaseAddBody_run (k : Nat) (s : AState) :
    let out := arun k s rootBaseAddBody
    out.regs rRhsBase = (s.regs rOldL + s.regs rRhsBase) % M ∧
      out.regs rOldL = s.regs rOldL ∧
      out.regs rBad = s.regs rBad ∧ out.arr = s.arr := by
  rw [rootBaseAddBody, arun_lift]
  simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rRhsBase, rOldL, rBad]

theorem rootAddBody_zero_sound (k : Nat) (s : AState)
    (hOld : s.regs rOldL < M) (hRhs : s.regs rRhsBase < M)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hzero : (arun k s rootAddBody).regs rBad = 0) :
    s.regs rBad = 0 ∧ s.regs rOldL + s.regs rRhsBase < M ∧
      (arun k s rootAddBody).regs rRhsBase =
        s.regs rOldL + s.regs rRhsBase ∧
      (arun k s rootAddBody).arr = s.arr := by
  let a := arun k s rootBaseAddBody
  let out := arun k a rootBaseCheckBody
  let q := (s.regs rOldL + s.regs rRhsBase) % M
  have ha := rootBaseAddBody_run k s
  change a.regs rRhsBase = q ∧ a.regs rOldL = s.regs rOldL ∧
    a.regs rBad = s.regs rBad ∧ a.arr = s.arr at ha
  have haword : ∀ j, a.regs j < M :=
    arun_regs_word k rootBaseAddBody s hword harr
  have hc := wrapCheckBody_run k rRhsBase rOldL a haword
  change out.regs rBad =
      (a.regs rBad ||| (if a.regs rRhsBase < a.regs rOldL then 1 else 0)) ∧
    out.arr = a.arr at hc
  have hout : arun k s rootAddBody = out := by
    simp only [rootAddBody, arun_append, a, out, rootBaseCheckBody]
  have houtR : out.regs rRhsBase = a.regs rRhsBase :=
    aframe k rRhsBase rootBaseCheckBody a (by rfl)
  have houtZero : out.regs rBad = 0 := by rw [← hout]; exact hzero
  have hz : s.regs rBad |||
      (if q < s.regs rOldL then 1 else 0) = 0 := by
    rw [← ha.2.2.1, ← ha.1, ← ha.2.1, ← hc.1]
    exact houtZero
  have hnot : ¬ q < s.regs rOldL := by
    intro h
    have := bor_eq_zero_right hz
    simp [h] at this
  have hsum := no_wrap_of_not_lt_left hOld hRhs hnot
  exact ⟨bor_eq_zero_left hz, hsum,
    hout.symm ▸ houtR.trans (ha.1.trans (Nat.mod_eq_of_lt hsum)),
    hout.symm ▸ hc.2.trans ha.2.2.2⟩

theorem rootTermBody_zero_sound (k : Nat) (s : AState)
    (hsq : s.regs rSqrt * s.regs rSqrt < M)
    (hs1 : s.regs rSqrt + 1 < M) (hspos : 0 < s.regs rSqrt)
    (hOld : s.regs rOldL < M)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hzero : (arun k s rootTermBody).regs rBad = 0) :
    let c := ceilRootOf (s.regs rN) (s.regs rSqrt)
    let q := RS62.fpD / c
    s.regs rBad = 0 ∧ c ≠ 0 ∧ 2 * q < M ∧
      s.regs rOldL + 2 * q < M ∧
      (arun k s rootTermBody).regs rRhsBase =
        s.regs rOldL + 2 * q ∧
      (arun k s rootTermBody).arr = s.arr := by
  dsimp only
  let c := arun k s rootCeilBody
  let d := arun k c rootDoubleBody
  let out := arun k d rootAddBody
  have hcRun := rootCeilBody_run k s hsq hs1
  change c.regs rCeilRoot = ceilRootOf (s.regs rN) (s.regs rSqrt) ∧
    c.regs rBad = s.regs rBad ∧ c.arr = s.arr at hcRun
  have hcword := arun_regs_word k rootCeilBody s hword harr
  have hcarr := arun_arr_word k rootCeilBody s hword harr
  have hdword := arun_regs_word k rootDoubleBody c hcword hcarr
  have hdarr := arun_arr_word k rootDoubleBody c hcword hcarr
  have hcOld : c.regs rOldL = s.regs rOldL :=
    aframe k rOldL rootCeilBody s (by rfl)
  have hdOld : d.regs rOldL = s.regs rOldL :=
    (aframe k rOldL rootDoubleBody c (by rfl)).trans hcOld
  have hcCeil : ceilRootOf (s.regs rN) (s.regs rSqrt) ≠ 0 := by
    unfold ceilRootOf
    omega
  have hccNe : c.regs rCeilRoot ≠ 0 := by rw [hcRun.1]; exact hcCeil
  have hout : arun k s rootTermBody = out := by
    simp only [rootTermBody, arun_append, c, d, out]
  have houtZero : out.regs rBad = 0 := by rw [← hout]; exact hzero
  have ha := rootAddBody_zero_sound k d
    (by rw [hdOld]; exact hOld) (hdword rRhsBase) hdword hdarr houtZero
  have hdBad : d.regs rBad = 0 := ha.1
  have hdRun := rootDoubleBody_zero_sound k c hccNe hcword hcarr hdBad
  change c.regs rBad = 0 ∧
      2 * (RS62.fpD / c.regs rCeilRoot) < M ∧
      d.regs rRhsBase = 2 * (RS62.fpD / c.regs rCeilRoot) ∧
      d.arr = c.arr at hdRun
  have hq : RS62.fpD / c.regs rCeilRoot =
      RS62.fpD / ceilRootOf (s.regs rN) (s.regs rSqrt) := by rw [hcRun.1]
  have hsBad : s.regs rBad = 0 := by
    rw [← hcRun.2.1]
    exact hdRun.1
  refine ⟨hsBad, hcCeil, ?_, ?_, ?_, ?_⟩
  · simpa only [hq] using hdRun.2.1
  · simpa only [hdOld, hdRun.2.2.1, hq] using ha.2.1
  · rw [hout, ha.2.2.1, hdOld, hdRun.2.2.1, hq]
  · rw [hout, ha.2.2.2, hdRun.2.2.2, hcRun.2.2]

theorem mulWide_run (k ra rb rlo rhi : Nat) (s : AState)
    (hD : Section413G1Denote.Distinct8 s0 s1 s2 s3 s4 s5 s6 s7)
    (hra : Section413G1Denote.NotIn8 ra s0 s1 s2 s3 s4 s5 s6 s7)
    (hrb : Section413G1Denote.NotIn8 rb s0 s1 s2 s3 s4 s5 s6 s7)
    (hrlo : Section413G1Denote.NotIn8 rlo s0 s1 s2 s3 s4 s5 s6 s7)
    (hrhi : Section413G1Denote.NotIn8 rhi s0 s1 s2 s3 s4 s5 s6 s7)
    (hlohi : rlo ≠ rhi) (hword : ∀ j, s.regs j < M) :
    let out := arun k s (mulWide ra rb rlo rhi)
    out.regs rlo = (MulWide.hl (s.regs ra) (s.regs rb)).1 ∧
      out.regs rhi = (MulWide.hl (s.regs ra) (s.regs rb)).2 ∧
      out.arr = s.arr := by
  rw [mulWide, arun_lift]
  have h := Section413G1Denote.mulWideG_hl k s.regs ra rb rlo rhi
    s0 s1 s2 s3 s4 s5 s6 s7
    hD hra hrb hrlo hrhi hlohi hword
  exact ⟨h.1, h.2, rfl⟩

theorem compareBody_run (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) :
    let out := arun k s compareBody
    out.regs rBad = s.regs rBad ||| s.regs rGate *
      (if s.regs rLhsHi < s.regs rRhsHi ∨
          (s.regs rLhsHi = s.regs rRhsHi ∧
            s.regs rLhsLo < s.regs rRhsLo) then 0 else 1) ∧
      out.regs rP = s.regs rPNext ∧ out.arr = s.arr := by
  rw [compareBody, arun_lift]
  have hbad : s.regs rBad % M = s.regs rBad :=
    Nat.mod_eq_of_lt (hword rBad)
  have hgate : s.regs rGate % M = s.regs rGate :=
    Nat.mod_eq_of_lt (hword rGate)
  have hbor : (s.regs rBad ||| s.regs rGate) % M =
      s.regs rBad ||| s.regs rGate := Nat.mod_eq_of_lt
    (Section413G1Denote.lor_lt_M (hword rBad) (hword rGate))
  have hbad' : s.regs 230 % M = s.regs 230 := by
    simpa only [rBad] using hbad
  have hgate' : s.regs 11 % M = s.regs 11 := by
    simpa only [rGate, RS62PrimeMaskLadder.rGate] using hgate
  have hbor' : (s.regs 230 ||| s.regs 11) % M =
      s.regs 230 ||| s.regs 11 := by
    simpa only [rBad, rGate, RS62PrimeMaskLadder.rGate] using hbor
  have hMne : M ≠ 1 := by decide
  by_cases hhi : s.regs 221 < s.regs 223 <;>
    by_cases heq : s.regs 221 = s.regs 223 <;>
    by_cases hlo : s.regs 220 < s.regs 222 <;>
    simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      rLhsHi, rRhsHi, rLhsLo, rRhsLo, rHiLt, rHiEq, rLoLt, rEqLoLt,
      rPass, rFail, rGate, rBad, rP, rPNext, hhi, heq, hlo,
      RS62PrimeMaskLadder.rGate, hbad', hgate', hbor', hMne,
      Nat.mod_eq_of_lt (hword rPNext)]

private theorem limbs_lt_iff {llo lhi rlo rhi : Nat}
    (hllo : llo < M) (hrlo : rlo < M) :
    llo + M * lhi < rlo + M * rhi ↔
      lhi < rhi ∨ (lhi = rhi ∧ llo < rlo) := by
  simp only [M] at hllo hrlo ⊢
  omega

theorem compareBody_zero_sound (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M)
    (hzero : (arun k s compareBody).regs rBad = 0) :
    s.regs rBad = 0 ∧
      (s.regs rGate = 1 →
        s.regs rLhsLo + M * s.regs rLhsHi <
          s.regs rRhsLo + M * s.regs rRhsHi) ∧
      (arun k s compareBody).regs rP = s.regs rPNext ∧
      (arun k s compareBody).arr = s.arr := by
  have hc := compareBody_run k s hword
  have hz : s.regs rBad ||| s.regs rGate *
      (if s.regs rLhsHi < s.regs rRhsHi ∨
          (s.regs rLhsHi = s.regs rRhsHi ∧
            s.regs rLhsLo < s.regs rRhsLo) then 0 else 1) = 0 :=
    hc.1.symm.trans hzero
  refine ⟨bor_eq_zero_left hz, ?_, hc.2.1, hc.2.2⟩
  intro hgate
  apply (limbs_lt_iff (hword rLhsLo) (hword rRhsLo)).2
  by_cases hlex : s.regs rLhsHi < s.regs rRhsHi ∨
      (s.regs rLhsHi = s.regs rRhsHi ∧
        s.regs rLhsLo < s.regs rRhsLo)
  · exact hlex
  · have hg0 := bor_eq_zero_right hz
    simp [hlex, hgate] at hg0

theorem lhsBody_run (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) :
    let out := arun k s lhsBody
    out.regs rLhsLo = (MulWide.hl (s.regs rPNext) (s.regs 235)).1 ∧
      out.regs rLhsHi = (MulWide.hl (s.regs rPNext) (s.regs 235)).2 ∧
      out.arr = s.arr := by
  simpa only [lhsBody] using mulWide_run k rPNext 235 rLhsLo rLhsHi s
    (by simp [Section413G1Denote.Distinct8, s0, s1, s2, s3, s4, s5, s6, s7])
    (by simp [Section413G1Denote.NotIn8, rPNext, s0, s1, s2, s3, s4, s5, s6, s7])
    (by simp [Section413G1Denote.NotIn8, s0, s1, s2, s3, s4, s5, s6, s7])
    (by simp [Section413G1Denote.NotIn8, rLhsLo, s0, s1, s2, s3, s4, s5, s6, s7])
    (by simp [Section413G1Denote.NotIn8, rLhsHi, s0, s1, s2, s3, s4, s5, s6, s7])
    (by decide)
    hword

theorem rhsBody_run (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) :
    let out := arun k s rhsBody
    out.regs rRhsLo = (MulWide.hl (s.regs rRhsBase) (s.regs 236)).1 ∧
      out.regs rRhsHi = (MulWide.hl (s.regs rRhsBase) (s.regs 236)).2 ∧
      out.arr = s.arr := by
  simpa only [rhsBody] using mulWide_run k rRhsBase 236 rRhsLo rRhsHi s
    (by simp [Section413G1Denote.Distinct8, s0, s1, s2, s3, s4, s5, s6, s7])
    (by simp [Section413G1Denote.NotIn8, rRhsBase, s0, s1, s2, s3, s4, s5, s6, s7])
    (by simp [Section413G1Denote.NotIn8, s0, s1, s2, s3, s4, s5, s6, s7])
    (by simp [Section413G1Denote.NotIn8, rRhsLo, s0, s1, s2, s3, s4, s5, s6, s7])
    (by simp [Section413G1Denote.NotIn8, rRhsHi, s0, s1, s2, s3, s4, s5, s6, s7])
    (by decide)
    hword

theorem guardBodies_zero_sound (k : Nat) (s : AState)
    (hcL : s.regs 235 = 10000000) (hcR : s.regs 236 = 17810724)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hzero : (arun k s guardBody).regs rBad = 0) :
    s.regs rBad = 0 ∧
      (s.regs rGate = 1 →
        s.regs rPNext * 10000000 < s.regs rRhsBase * 17810724) ∧
      (arun k s guardBody).regs rP = s.regs rPNext ∧
      (arun k s guardBody).arr = s.arr := by
  let l := arun k s lhsBody
  let r := arun k l rhsBody
  let out := arun k r compareBody
  have hl := lhsBody_run k s hword
  change l.regs rLhsLo = (MulWide.hl (s.regs rPNext) (s.regs 235)).1 ∧
    l.regs rLhsHi = (MulWide.hl (s.regs rPNext) (s.regs 235)).2 ∧
    l.arr = s.arr at hl
  have hlword := arun_regs_word k lhsBody s hword harr
  have hlarr := arun_arr_word k lhsBody s hword harr
  have hr := rhsBody_run k l hlword
  change r.regs rRhsLo = (MulWide.hl (l.regs rRhsBase) (l.regs 236)).1 ∧
    r.regs rRhsHi = (MulWide.hl (l.regs rRhsBase) (l.regs 236)).2 ∧
    r.arr = l.arr at hr
  have hrword := arun_regs_word k rhsBody l hlword hlarr
  have hout : arun k s guardBody = out := by
    simp only [guardBody, arun_append, l, r, out]
  have houtZero : out.regs rBad = 0 := by rw [← hout]; exact hzero
  have hc := compareBody_zero_sound k r hrword houtZero
  have hlPNext : l.regs rPNext = s.regs rPNext :=
    aframe k rPNext lhsBody s (by rfl)
  have hl235 : l.regs 235 = s.regs 235 := aframe k 235 lhsBody s (by rfl)
  have hlRhs : l.regs rRhsBase = s.regs rRhsBase :=
    aframe k rRhsBase lhsBody s (by rfl)
  have hl236 : l.regs 236 = s.regs 236 := aframe k 236 lhsBody s (by rfl)
  have hlBad : l.regs rBad = s.regs rBad := aframe k rBad lhsBody s (by rfl)
  have hlGate : l.regs rGate = s.regs rGate := aframe k rGate lhsBody s (by rfl)
  have hrLlo : r.regs rLhsLo = l.regs rLhsLo :=
    aframe k rLhsLo rhsBody l (by rfl)
  have hrLhi : r.regs rLhsHi = l.regs rLhsHi :=
    aframe k rLhsHi rhsBody l (by rfl)
  have hrPNext : r.regs rPNext = s.regs rPNext :=
    (aframe k rPNext rhsBody l (by rfl)).trans hlPNext
  have hrBad : r.regs rBad = s.regs rBad :=
    (aframe k rBad rhsBody l (by rfl)).trans hlBad
  have hrGate : r.regs rGate = s.regs rGate :=
    (aframe k rGate rhsBody l (by rfl)).trans hlGate
  have hlspec := MulWide.hl_spec (s.regs rPNext) (s.regs 235)
    (by simpa only [MulWide.B64, M] using hword rPNext)
    (by simpa only [MulWide.B64, M] using hword 235)
  have hrspec := MulWide.hl_spec (s.regs rRhsBase) (s.regs 236)
    (by simpa only [MulWide.B64, M] using hword rRhsBase)
    (by simpa only [MulWide.B64, M] using hword 236)
  have hguard : s.regs rGate = 1 →
      s.regs rPNext * 10000000 < s.regs rRhsBase * 17810724 := by
    intro hgate
    have hm := hc.2.1 (by rw [hrGate]; exact hgate)
    rw [hrLlo, hrLhi, hl.1, hl.2.1, hr.1, hr.2.1,
      hlRhs, hl236] at hm
    have hlexact :
        (MulWide.hl (s.regs rPNext) (s.regs 235)).1 +
            M * (MulWide.hl (s.regs rPNext) (s.regs 235)).2 =
          s.regs rPNext * s.regs 235 := by
      simpa only [MulWide.B64, M] using hlspec.1
    have hrexact :
        (MulWide.hl (s.regs rRhsBase) (s.regs 236)).1 +
            M * (MulWide.hl (s.regs rRhsBase) (s.regs 236)).2 =
          s.regs rRhsBase * s.regs 236 := by
      simpa only [MulWide.B64, M] using hrspec.1
    rw [hlexact, hrexact, hcL, hcR] at hm
    exact hm
  refine ⟨?_, hguard, ?_, ?_⟩
  · rw [← hrBad]
    exact hc.1
  · rw [hout, hc.2.2.1, hrPNext]
  · rw [hout, hc.2.2.2, hr.2.2, hl.2.2]

theorem sqrtAdvanceBody_run (k : Nat) (s : AState)
    (hs1 : s.regs rSqrt + 1 < M)
    (hsq : (s.regs rSqrt + 1) * (s.regs rSqrt + 1) < M)
    (hn1 : s.regs rN + 1 < M) :
    let out := arun k s sqrtAdvanceBody
    out.regs rSqrt = sqrtNext (s.regs rN) (s.regs rSqrt) ∧
      out.arr = s.arr := by
  rw [sqrtAdvanceBody, arun_lift]
  have hs1M : (s.regs rSqrt + 1) % M = s.regs rSqrt + 1 :=
    Nat.mod_eq_of_lt hs1
  have hsqM : ((s.regs rSqrt + 1) * (s.regs rSqrt + 1)) % M =
      (s.regs rSqrt + 1) * (s.regs rSqrt + 1) := Nat.mod_eq_of_lt hsq
  have hn1M : (s.regs rN + 1) % M = s.regs rN + 1 :=
    Nat.mod_eq_of_lt hn1
  have hs1M' : (s.regs 214 + 1) % M = s.regs 214 + 1 := by
    simpa only [rSqrt] using hs1M
  have hsqM' : ((s.regs 214 + 1) * (s.regs 214 + 1)) % M =
      (s.regs 214 + 1) * (s.regs 214 + 1) := by
    simpa only [rSqrt] using hsqM
  have hn1M' : (s.regs 132 + 1) % M = s.regs 132 + 1 := by
    simpa only [rN, RS62PrimeMaskLadder.rN] using hn1M
  by_cases h : (s.regs rSqrt + 1) * (s.regs rSqrt + 1) ≤
      s.regs rN + 1
  · have h' : (s.regs 214 + 1) * (s.regs 214 + 1) ≤
        s.regs 132 + 1 := by
      simpa only [rSqrt, rN, RS62PrimeMaskLadder.rN] using h
    simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      rS1, rS1Sq, rN1, rSqrtBump, rSqrt, rN,
      RS62PrimeMaskLadder.rN, hs1M', hsqM', hn1M', h', sqrtNext]
  · have hsM : s.regs rSqrt % M = s.regs rSqrt :=
      Nat.mod_eq_of_lt (by omega)
    have hsM' : s.regs 214 % M = s.regs 214 := by
      simpa only [rSqrt] using hsM
    have h' : ¬ (s.regs 214 + 1) * (s.regs 214 + 1) ≤
        s.regs 132 + 1 := by
      simpa only [rSqrt, rN, RS62PrimeMaskLadder.rN] using h
    simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      rS1, rS1Sq, rN1, rSqrtBump, rSqrt, rN,
      RS62PrimeMaskLadder.rN, hs1M', hsqM', hn1M', h', sqrtNext, hsM']

theorem denominatorAdvanceBody_run (k : Nat) (s : AState)
    (hden : s.regs 237 + 1 < M) (hnm2 : s.regs rNm2 + 1 < M) :
    let out := arun k s denominatorAdvanceBody
    out.regs 237 = s.regs 237 + 1 ∧
      out.regs rNm2 = s.regs rNm2 + 1 ∧ out.arr = s.arr := by
  rw [denominatorAdvanceBody, arun_lift]
  have hnm2' : (s.regs 238 + 1) % M = s.regs 238 + 1 := by
    apply Nat.mod_eq_of_lt
    simpa only [rNm2] using hnm2
  simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rNm2, Nat.mod_eq_of_lt hden, hnm2']

theorem overflowBody_gate_n (n0 k : Nat) (s : AState)
    (hkM : k < M) (hnM : (n0 - 1) + k < M) :
    let out := arun k s (RS62PrimeMaskLadderOverflow.body n0)
    out.regs rGate = s.arr k ∧ out.regs rN = (n0 - 1) + k ∧
      out.arr = s.arr := by
  let saved := arun k s RS62PrimeMaskLadderOverflow.saveBody
  let pre := arun k saved (RS62PrimeMaskLadder.maskPrefix n0)
  let cand := arun k pre
    RamareCombined100M.LogSweep.candidateBody
  let out := arun k cand RS62PrimeMaskLadderOverflow.checkBody
  have hsArr : saved.arr = s.arr := by
    simp [saved, RS62PrimeMaskLadderOverflow.saveBody, arun, astep,
      AState.writeReg]
  have hp := RS62PrimeMaskLadder.maskPrefix_run n0 k saved hkM hnM
  change pre.regs RS62PrimeMaskLadder.rAddr = k ∧
    pre.regs rGate = saved.arr k ∧ pre.regs rN = (n0 - 1) + k ∧
    pre.regs rLogL = saved.regs rLogL ∧
    pre.regs rLogU = saved.regs rLogU ∧ pre.arr = saved.arr at hp
  have hcGate : cand.regs rGate = pre.regs rGate :=
    aframe k rGate RamareCombined100M.LogSweep.candidateBody pre (by rfl)
  have hcN : cand.regs rN = pre.regs rN :=
    aframe k rN RamareCombined100M.LogSweep.candidateBody pre (by rfl)
  have hcArr : cand.arr = pre.arr := by
    simp [cand, RamareCombined100M.LogSweep.candidateBody, arun_append,
      arun_lift_arr]
  have hoGate : out.regs rGate = cand.regs rGate :=
    aframe k rGate RS62PrimeMaskLadderOverflow.checkBody cand (by rfl)
  have hoN : out.regs rN = cand.regs rN :=
    aframe k rN RS62PrimeMaskLadderOverflow.checkBody cand (by rfl)
  have hout : arun k s (RS62PrimeMaskLadderOverflow.body n0) = out := by
    simp only [RS62PrimeMaskLadderOverflow.body,
      RS62PrimeMaskLadder.body, arun_append, saved, pre, cand, out]
  dsimp only
  refine ⟨?_, ?_, RS62PrimeMaskLadderOverflow.body_arr n0 k s⟩
  · rw [hout, hoGate, hcGate, hp.2.1, hsArr]
  · rw [hout, hoN, hcN, hp.2.2.1]

/-- The corrected §4.10 logarithm body advances at every integer, while the
restored gate remains the prime-mask bit used by the product and guard. -/
theorem ungatedLogBody_zero_sound (n0 k : Nat) (s : AState)
    (hkM : k < M) (hn2 : 2 ≤ (n0 - 1) + k)
    (hn40 : (n0 - 1) + k ≤ 2 ^ 40)
    (hnM : (n0 - 1) + k < M)
    (hLogL : s.regs rLogL < M) (hLogU : s.regs rLogU < M)
    (hBad : s.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1)
    (hZero : (arun k s (ungatedLogBody n0)).regs
      RS62PrimeMaskLadderOverflow.rBad = 0) :
    s.regs RS62PrimeMaskLadderOverflow.rBad = 0 ∧
      s.regs rLogL + RS62.incLWord ((n0 - 1) + k) < M ∧
      s.regs rLogU + RS62.incUWord ((n0 - 1) + k) < M ∧
      (arun k s (ungatedLogBody n0)).regs rLogL =
        s.regs rLogL + RS62.incLWord ((n0 - 1) + k) ∧
      (arun k s (ungatedLogBody n0)).regs rLogU =
        s.regs rLogU + RS62.incUWord ((n0 - 1) + k) ∧
      (arun k s (ungatedLogBody n0)).regs rGate = s.arr k ∧
      (arun k s (ungatedLogBody n0)).regs rN = (n0 - 1) + k ∧
      (arun k s (ungatedLogBody n0)).arr = s.arr := by
  let saved := arun k s RS62PrimeMaskLadderOverflow.saveBody
  let pre := arun k saved (RS62PrimeMaskLadder.maskPrefix n0)
  let forced := arun k pre (lift
    [ .mov rPrimeGate (.reg rGate), .mov rGate (.lit 1) ])
  let cand := arun k forced RamareCombined100M.LogSweep.candidateBody
  let checked := arun k cand RS62PrimeMaskLadderOverflow.checkBody
  let out := arun k checked (lift [ .mov rGate (.reg rPrimeGate) ])
  have hs := RS62PrimeMaskLadderOverflow.saveBody_run k s
  change saved.regs RS62PrimeMaskLadderOverflow.rOldL = s.regs rLogL ∧
    saved.regs RS62PrimeMaskLadderOverflow.rOldU = s.regs rLogU ∧
    saved.regs rLogL = s.regs rLogL ∧ saved.regs rLogU = s.regs rLogU ∧
    saved.regs RS62PrimeMaskLadderOverflow.rBad =
      s.regs RS62PrimeMaskLadderOverflow.rBad ∧ saved.arr = s.arr at hs
  have hp := RS62PrimeMaskLadder.maskPrefix_run n0 k saved hkM hnM
  change pre.regs RS62PrimeMaskLadder.rAddr = k ∧
    pre.regs rGate = saved.arr k ∧ pre.regs rN = (n0 - 1) + k ∧
    pre.regs rLogL = saved.regs rLogL ∧
    pre.regs rLogU = saved.regs rLogU ∧ pre.arr = saved.arr at hp
  have hpOldL : pre.regs RS62PrimeMaskLadderOverflow.rOldL =
      saved.regs RS62PrimeMaskLadderOverflow.rOldL :=
    aframe k _ (RS62PrimeMaskLadder.maskPrefix n0) saved (by rfl)
  have hpOldU : pre.regs RS62PrimeMaskLadderOverflow.rOldU =
      saved.regs RS62PrimeMaskLadderOverflow.rOldU :=
    aframe k _ (RS62PrimeMaskLadder.maskPrefix n0) saved (by rfl)
  have hpBad : pre.regs RS62PrimeMaskLadderOverflow.rBad =
      saved.regs RS62PrimeMaskLadderOverflow.rBad :=
    aframe k _ (RS62PrimeMaskLadder.maskPrefix n0) saved (by rfl)
  have hf : forced.regs rPrimeGate = pre.regs rGate ∧
      forced.regs rGate = 1 ∧ forced.regs rN = pre.regs rN ∧
      forced.regs rLogL = pre.regs rLogL ∧
      forced.regs rLogU = pre.regs rLogU ∧
      forced.regs RS62PrimeMaskLadderOverflow.rOldL =
        pre.regs RS62PrimeMaskLadderOverflow.rOldL ∧
      forced.regs RS62PrimeMaskLadderOverflow.rOldU =
        pre.regs RS62PrimeMaskLadderOverflow.rOldU ∧
      forced.regs RS62PrimeMaskLadderOverflow.rBad =
        pre.regs RS62PrimeMaskLadderOverflow.rBad ∧ forced.arr = pre.arr := by
    change forced.regs 209 = pre.regs 11 ∧ forced.regs 11 = 1 ∧
      forced.regs 132 = pre.regs 132 ∧ forced.regs 180 = pre.regs 180 ∧
      forced.regs 181 = pre.regs 181 ∧ forced.regs 200 = pre.regs 200 ∧
      forced.regs 201 = pre.regs 201 ∧ forced.regs 205 = pre.regs 205 ∧
      forced.arr = pre.arr
    have hrGate : rGate = 11 := rfl
    simp [forced, arun, astep, AState.writeReg, sdest, sval, denoteOperand,
      hrGate,
      rPrimeGate, RS62PrimeMaskLadder.rGate, RS62PrimeMaskLadder.rN,
      RS62PrimeMaskLadder.rLogL, RS62PrimeMaskLadder.rLogU,
      RamareCombined100M.LogSweep.rLogL,
      RamareCombined100M.LogSweep.rLogU, M,
      RS62PrimeMaskLadderOverflow.rOldL,
      RS62PrimeMaskLadderOverflow.rOldU,
      RS62PrimeMaskLadderOverflow.rBad]
  have hc := RS62PrimeMaskLadderOverflow.candidateBody_run_mod k forced
    (by rw [hf.2.2.1, hp.2.2.1]; exact hn2)
    (by rw [hf.2.2.1, hp.2.2.1]; exact hn40)
    (by rw [hf.2.1]; decide)
  have hcOldL : cand.regs RS62PrimeMaskLadderOverflow.rOldL =
      forced.regs RS62PrimeMaskLadderOverflow.rOldL :=
    RS62PrimeMaskLadderOverflow.candidateBody_frame k _ forced (by decide)
  have hcOldU : cand.regs RS62PrimeMaskLadderOverflow.rOldU =
      forced.regs RS62PrimeMaskLadderOverflow.rOldU :=
    RS62PrimeMaskLadderOverflow.candidateBody_frame k _ forced (by decide)
  have hcBad : cand.regs RS62PrimeMaskLadderOverflow.rBad =
      forced.regs RS62PrimeMaskLadderOverflow.rBad :=
    RS62PrimeMaskLadderOverflow.candidateBody_frame k _ forced (by decide)
  have hcheck := RS62PrimeMaskLadderOverflow.checkBody_run k cand (by
    change cand.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1
    rw [hcBad, hf.2.2.2.2.2.2.2.1, hpBad, hs.2.2.2.2.1]
    exact hBad)
  change checked.regs RS62PrimeMaskLadderOverflow.rBad =
      (cand.regs RS62PrimeMaskLadderOverflow.rBad |||
        ((if cand.regs rLogL <
            cand.regs RS62PrimeMaskLadderOverflow.rOldL then 1 else 0) |||
         (if cand.regs rLogU <
            cand.regs RS62PrimeMaskLadderOverflow.rOldU then 1 else 0))) ∧
    checked.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1 ∧
    checked.regs rLogL = cand.regs rLogL ∧
    checked.regs rLogU = cand.regs rLogU ∧ checked.arr = cand.arr at hcheck
  have houtEq : arun k s (ungatedLogBody n0) = out := by
    simp only [ungatedLogBody, arun_append, saved, pre, forced, cand,
      checked, out]
  have hrestore : out.regs rGate = checked.regs rPrimeGate ∧
      out.regs rLogL = checked.regs rLogL ∧
      out.regs rLogU = checked.regs rLogU ∧ out.regs rN = checked.regs rN ∧
      out.regs RS62PrimeMaskLadderOverflow.rBad =
        checked.regs RS62PrimeMaskLadderOverflow.rBad ∧ out.arr = checked.arr := by
    change out.regs 11 = checked.regs 209 ∧
      out.regs 180 = checked.regs 180 ∧ out.regs 181 = checked.regs 181 ∧
      out.regs 132 = checked.regs 132 ∧ out.regs 205 = checked.regs 205 ∧
      out.arr = checked.arr
    have hrGate : rGate = 11 := rfl
    simp [out, arun, astep, AState.writeReg, sdest, sval, denoteOperand,
      hrGate,
      rPrimeGate, RS62PrimeMaskLadder.rGate, RS62PrimeMaskLadder.rN,
      RS62PrimeMaskLadder.rLogL, RS62PrimeMaskLadder.rLogU,
      RamareCombined100M.LogSweep.rLogL,
      RamareCombined100M.LogSweep.rLogU,
      RS62PrimeMaskLadderOverflow.rBad]
  have houtZero : checked.regs RS62PrimeMaskLadderOverflow.rBad = 0 := by
    rw [← hrestore.2.2.2.2.1, ← houtEq]
    exact hZero
  have hz := RS62PrimeMaskLadderOverflow.or_eq_zero
    (hcheck.1.symm.trans houtZero)
  have hflags := RS62PrimeMaskLadderOverflow.or_eq_zero hz.2
  have hnL : ¬ cand.regs rLogL <
      cand.regs RS62PrimeMaskLadderOverflow.rOldL := by
    intro h
    simp [h] at hflags
  have hnU : ¬ cand.regs rLogU <
      cand.regs RS62PrimeMaskLadderOverflow.rOldU := by
    intro h
    simp [h] at hflags
  change cand.regs rLogL =
      (forced.regs rLogL + forced.regs rGate *
        RS62.incLWord (forced.regs rN)) % M ∧
    cand.regs rLogU =
      (forced.regs rLogU + forced.regs rGate *
        RS62.incUWord (forced.regs rN)) % M ∧ _ at hc
  have hcL : cand.regs rLogL =
      (s.regs rLogL + RS62.incLWord ((n0 - 1) + k)) % M := by
    rw [hc.1, hf.2.2.2.1, hp.2.2.2.1, hs.2.2.1, hf.2.1,
      Nat.one_mul, hf.2.2.1, hp.2.2.1]
  have hcU : cand.regs rLogU =
      (s.regs rLogU + RS62.incUWord ((n0 - 1) + k)) % M := by
    rw [hc.2.1, hf.2.2.2.2.1, hp.2.2.2.2.1, hs.2.2.2.1, hf.2.1,
      Nat.one_mul, hf.2.2.1, hp.2.2.1]
  have holdL : cand.regs RS62PrimeMaskLadderOverflow.rOldL =
      s.regs rLogL := by rw [hcOldL, hf.2.2.2.2.2.1, hpOldL, hs.1]
  have holdU : cand.regs RS62PrimeMaskLadderOverflow.rOldU =
      s.regs rLogU := by rw [hcOldU, hf.2.2.2.2.2.2.1, hpOldU, hs.2.1]
  have hdL : RS62.incLWord ((n0 - 1) + k) < M :=
    Nat.lt_of_le_of_lt (RS62.incLWord_le _) (by decide)
  have hdU : RS62.incUWord ((n0 - 1) + k) < M := by
    apply Nat.lt_of_le_of_lt (RS62.incUWord_le _)
    apply Nat.lt_of_le_of_lt (Nat.add_le_add_left hn40 RS62.fpD)
    decide
  have hsumL : s.regs rLogL + RS62.incLWord ((n0 - 1) + k) < M :=
    RS62PrimeMaskLadderOverflow.no_wrap_of_not_lt_left hLogL hdL
      (by rw [← hcL, ← holdL]; exact hnL)
  have hsumU : s.regs rLogU + RS62.incUWord ((n0 - 1) + k) < M :=
    RS62PrimeMaskLadderOverflow.no_wrap_of_not_lt_left hLogU hdU
      (by rw [← hcU, ← holdU]; exact hnU)
  have hcheckedGate : checked.regs rPrimeGate = forced.regs rPrimeGate :=
    aframe k rPrimeGate
      (RamareCombined100M.LogSweep.candidateBody ++
        RS62PrimeMaskLadderOverflow.checkBody) forced (by rfl)
  refine ⟨?_, hsumL, hsumU, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hs.2.2.2.2.1, ← hpBad, ← hf.2.2.2.2.2.2.2.1, ← hcBad]
    exact hz.1
  · rw [houtEq, hrestore.2.1, hcheck.2.2.1, hcL,
      Nat.mod_eq_of_lt hsumL]
  · rw [houtEq, hrestore.2.2.1, hcheck.2.2.2.1, hcU,
      Nat.mod_eq_of_lt hsumU]
  · rw [houtEq, hrestore.1, hcheckedGate, hf.1, hp.2.1, hs.2.2.2.2.2]
  · rw [houtEq, hrestore.2.2.2.1]
    rw [aframe k rN RS62PrimeMaskLadderOverflow.checkBody cand (by rfl)]
    rw [RS62PrimeMaskLadderOverflow.candidateBody_frame k rN forced (by decide),
      hf.2.2.1, hp.2.2.1]
  · rw [houtEq, hrestore.2.2.2.2.2, hcheck.2.2.2.2]
    exact hc.2.2.2.2.2.trans
      (hf.2.2.2.2.2.2.2.2.trans
        (hp.2.2.2.2.2.trans hs.2.2.2.2.2))

/-- Static facts for the corrected logarithm body.  In particular, the
overflow flag remains a sticky bit even when the final run is not assumed
clean. -/
theorem ungatedLogBody_static (n0 k : Nat) (s : AState)
    (hkM : k < M) (hnM : (n0 - 1) + k < M)
    (hBad : s.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1) :
    let out := arun k s (ungatedLogBody n0)
    out.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1 ∧
      s.regs RS62PrimeMaskLadderOverflow.rBad ≤
        out.regs RS62PrimeMaskLadderOverflow.rBad ∧
      out.regs rGate = s.arr k ∧ out.regs rN = (n0 - 1) + k ∧
      out.arr = s.arr := by
  let saved := arun k s RS62PrimeMaskLadderOverflow.saveBody
  let pre := arun k saved (RS62PrimeMaskLadder.maskPrefix n0)
  let forced := arun k pre (lift
    [ .mov rPrimeGate (.reg rGate), .mov rGate (.lit 1) ])
  let cand := arun k forced RamareCombined100M.LogSweep.candidateBody
  let checked := arun k cand RS62PrimeMaskLadderOverflow.checkBody
  let out := arun k checked (lift [ .mov rGate (.reg rPrimeGate) ])
  have hs := RS62PrimeMaskLadderOverflow.saveBody_run k s
  change saved.regs RS62PrimeMaskLadderOverflow.rOldL = s.regs rLogL ∧
    saved.regs RS62PrimeMaskLadderOverflow.rOldU = s.regs rLogU ∧
    saved.regs rLogL = s.regs rLogL ∧ saved.regs rLogU = s.regs rLogU ∧
    saved.regs RS62PrimeMaskLadderOverflow.rBad =
      s.regs RS62PrimeMaskLadderOverflow.rBad ∧ saved.arr = s.arr at hs
  have hp := RS62PrimeMaskLadder.maskPrefix_run n0 k saved hkM hnM
  change pre.regs RS62PrimeMaskLadder.rAddr = k ∧
    pre.regs rGate = saved.arr k ∧ pre.regs rN = (n0 - 1) + k ∧
    pre.regs rLogL = saved.regs rLogL ∧
    pre.regs rLogU = saved.regs rLogU ∧ pre.arr = saved.arr at hp
  have hpBad : pre.regs RS62PrimeMaskLadderOverflow.rBad =
      saved.regs RS62PrimeMaskLadderOverflow.rBad :=
    aframe k _ (RS62PrimeMaskLadder.maskPrefix n0) saved (by rfl)
  have hf : forced.regs rPrimeGate = pre.regs rGate ∧
      forced.regs RS62PrimeMaskLadderOverflow.rBad =
        pre.regs RS62PrimeMaskLadderOverflow.rBad ∧
      forced.arr = pre.arr := by
    change forced.regs 209 = pre.regs 11 ∧ forced.regs 205 = pre.regs 205 ∧
      forced.arr = pre.arr
    have hrGate : rGate = 11 := rfl
    simp [forced, arun, astep, AState.writeReg, sdest, sval, denoteOperand,
      hrGate, rPrimeGate, RS62PrimeMaskLadderOverflow.rBad]
  have hcPrime : cand.regs rPrimeGate = forced.regs rPrimeGate :=
    RS62PrimeMaskLadderOverflow.candidateBody_frame k _ forced (by decide)
  have hcBad : cand.regs RS62PrimeMaskLadderOverflow.rBad =
      forced.regs RS62PrimeMaskLadderOverflow.rBad :=
    RS62PrimeMaskLadderOverflow.candidateBody_frame k _ forced (by decide)
  have hcN : cand.regs rN = forced.regs rN :=
    RS62PrimeMaskLadderOverflow.candidateBody_frame k _ forced (by decide)
  have hcArr : cand.arr = forced.arr := by
    simp [cand, RamareCombined100M.LogSweep.candidateBody, arun_append,
      arun_lift_arr]
  have hcheck := RS62PrimeMaskLadderOverflow.checkBody_run k cand (by
    change cand.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1
    rw [hcBad, hf.2.1, hpBad, hs.2.2.2.2.1]
    exact hBad)
  change checked.regs RS62PrimeMaskLadderOverflow.rBad =
      (cand.regs RS62PrimeMaskLadderOverflow.rBad |||
        ((if cand.regs rLogL <
            cand.regs RS62PrimeMaskLadderOverflow.rOldL then 1 else 0) |||
         (if cand.regs rLogU <
            cand.regs RS62PrimeMaskLadderOverflow.rOldU then 1 else 0))) ∧
    checked.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1 ∧
    checked.regs rLogL = cand.regs rLogL ∧
    checked.regs rLogU = cand.regs rLogU ∧ checked.arr = cand.arr at hcheck
  have hcheckPrime : checked.regs rPrimeGate = cand.regs rPrimeGate :=
    aframe k rPrimeGate RS62PrimeMaskLadderOverflow.checkBody cand (by rfl)
  have hcheckN : checked.regs rN = cand.regs rN :=
    aframe k rN RS62PrimeMaskLadderOverflow.checkBody cand (by rfl)
  have hrestore : out.regs rGate = checked.regs rPrimeGate ∧
      out.regs RS62PrimeMaskLadderOverflow.rBad =
        checked.regs RS62PrimeMaskLadderOverflow.rBad ∧
      out.regs rN = checked.regs rN ∧ out.arr = checked.arr := by
    change out.regs 11 = checked.regs 209 ∧ out.regs 205 = checked.regs 205 ∧
      out.regs 132 = checked.regs 132 ∧ out.arr = checked.arr
    have hrGate : rGate = 11 := rfl
    simp [out, arun, astep, AState.writeReg, sdest, sval, denoteOperand,
      hrGate, rPrimeGate, RS62PrimeMaskLadderOverflow.rBad]
  have houtEq : arun k s (ungatedLogBody n0) = out := by
    simp only [ungatedLogBody, arun_append, saved, pre, forced, cand,
      checked, out]
  have hmono : s.regs RS62PrimeMaskLadderOverflow.rBad ≤
      out.regs RS62PrimeMaskLadderOverflow.rBad := by
    calc
      s.regs RS62PrimeMaskLadderOverflow.rBad = cand.regs
          RS62PrimeMaskLadderOverflow.rBad := by
        rw [hcBad, hf.2.1, hpBad, hs.2.2.2.2.1]
      _ ≤ cand.regs RS62PrimeMaskLadderOverflow.rBad |||
          ((if cand.regs rLogL <
              cand.regs RS62PrimeMaskLadderOverflow.rOldL then 1 else 0) |||
           (if cand.regs rLogU <
              cand.regs RS62PrimeMaskLadderOverflow.rOldU then 1 else 0)) :=
        Nat.left_le_or
      _ = checked.regs RS62PrimeMaskLadderOverflow.rBad := hcheck.1.symm
      _ = out.regs RS62PrimeMaskLadderOverflow.rBad := hrestore.2.1.symm
  dsimp only
  rw [houtEq]
  refine ⟨?_, hmono, ?_, ?_, ?_⟩
  · rw [hrestore.2.1]
    exact hcheck.2.1
  · rw [hrestore.1, hcheckPrime, hcPrime, hf.1, hp.2.1,
      hs.2.2.2.2.2]
  · rw [hrestore.2.2.1, hcheckN, hcN]
    have hfN : forced.regs rN = pre.regs rN := by
      exact aframe k rN (lift
        [ .mov rPrimeGate (.reg rGate), .mov rGate (.lit 1) ]) pre (by rfl)
    rw [hfN, hp.2.2.1]
  · rw [hrestore.2.2.2, hcheck.2.2.2.2, hcArr, hf.2.2,
      hp.2.2.2.2.2, hs.2.2.2.2.2]

theorem postGuardBody_zero_sound (k : Nat) (s : AState)
    (hcL : s.regs 235 = 10000000) (hcR : s.regs 236 = 17810724)
    (hs1 : s.regs rSqrt + 1 < M)
    (hsq : (s.regs rSqrt + 1) * (s.regs rSqrt + 1) < M)
    (hn1 : s.regs rN + 1 < M)
    (hden : s.regs 237 + 1 < M) (hnm2 : s.regs rNm2 + 1 < M)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hzero : (arun k s postGuardBody).regs rBad = 0) :
    s.regs rBad = 0 ∧
      (s.regs rGate = 1 →
        s.regs rPNext * 10000000 < s.regs rRhsBase * 17810724) ∧
      (arun k s postGuardBody).regs rP = s.regs rPNext ∧
      (arun k s postGuardBody).regs rSqrt =
        sqrtNext (s.regs rN) (s.regs rSqrt) ∧
      (arun k s postGuardBody).regs 237 = s.regs 237 + 1 ∧
      (arun k s postGuardBody).regs rNm2 = s.regs rNm2 + 1 ∧
      (arun k s postGuardBody).arr = s.arr := by
  let f := arun k s guardBody
  let g := arun k f sqrtAdvanceBody
  let out := arun k g denominatorAdvanceBody
  have hfword := arun_regs_word k guardBody s hword harr
  have hfarr := arun_arr_word k guardBody s hword harr
  have hgword := arun_regs_word k sqrtAdvanceBody f hfword hfarr
  have hfBad : f.regs rBad = 0 := by
    have hoBad : out.regs rBad = g.regs rBad :=
      aframe k rBad denominatorAdvanceBody g (by rfl)
    have hgBad : g.regs rBad = f.regs rBad :=
      aframe k rBad sqrtAdvanceBody f (by rfl)
    have hout : arun k s postGuardBody = out := by
      simp only [postGuardBody, arun_append, f, g, out]
    rw [← hgBad, ← hoBad, ← hout]
    exact hzero
  have hguard := guardBodies_zero_sound k s hcL hcR hword harr hfBad
  have hfSqrt : f.regs rSqrt = s.regs rSqrt :=
    aframe k rSqrt guardBody s (by rfl)
  have hfN : f.regs rN = s.regs rN := aframe k rN guardBody s (by rfl)
  have hfDen : f.regs 237 = s.regs 237 := aframe k 237 guardBody s (by rfl)
  have hfNm2 : f.regs rNm2 = s.regs rNm2 :=
    aframe k rNm2 guardBody s (by rfl)
  have hsqrt := sqrtAdvanceBody_run k f
    (by rw [hfSqrt]; exact hs1) (by rw [hfSqrt]; exact hsq)
    (by rw [hfN]; exact hn1)
  change g.regs rSqrt = sqrtNext (f.regs rN) (f.regs rSqrt) ∧
    g.arr = f.arr at hsqrt
  have hgDen : g.regs 237 = s.regs 237 :=
    (aframe k 237 sqrtAdvanceBody f (by rfl)).trans hfDen
  have hgNm2 : g.regs rNm2 = s.regs rNm2 :=
    (aframe k rNm2 sqrtAdvanceBody f (by rfl)).trans hfNm2
  have hdenRun := denominatorAdvanceBody_run k g
    (by rw [hgDen]; exact hden) (by rw [hgNm2]; exact hnm2)
  change out.regs 237 = g.regs 237 + 1 ∧
    out.regs rNm2 = g.regs rNm2 + 1 ∧ out.arr = g.arr at hdenRun
  have hfP : f.regs rP = s.regs rPNext := hguard.2.2.1
  have hgP : g.regs rP = f.regs rP :=
    aframe k rP sqrtAdvanceBody f (by rfl)
  have hoP : out.regs rP = g.regs rP :=
    aframe k rP denominatorAdvanceBody g (by rfl)
  have hoSqrt : out.regs rSqrt = g.regs rSqrt :=
    aframe k rSqrt denominatorAdvanceBody g (by rfl)
  have hout : arun k s postGuardBody = out := by
    simp only [postGuardBody, arun_append, f, g, out]
  refine ⟨hguard.1, hguard.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hout, hoP, hgP, hfP]
  · rw [hout, hoSqrt]
    simpa only [hfN, hfSqrt] using hsqrt.1
  · rw [hout, hdenRun.1, hgDen]
  · rw [hout, hdenRun.2.1, hgNm2]
  · rw [hout, hdenRun.2.2, hsqrt.2, hguard.2.2.2]

theorem arithmeticBody_zero_sound (k : Nat) (s : AState)
    (hP : s.regs rP < M) (hnm2W : s.regs rNm2 < M)
    (hGate : s.regs rGate ≤ 1) (hdenNe : s.regs 237 ≠ 0)
    (hsq : s.regs rSqrt * s.regs rSqrt < M)
    (hs1 : s.regs rSqrt + 1 < M) (hspos : 0 < s.regs rSqrt)
    (hs1sq : (s.regs rSqrt + 1) * (s.regs rSqrt + 1) < M)
    (hn1 : s.regs rN + 1 < M) (hOld : s.regs rOldL < M)
    (hden : s.regs 237 + 1 < M) (hnm2 : s.regs rNm2 + 1 < M)
    (hcL : s.regs 235 = 10000000) (hcR : s.regs 236 = 17810724)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hzero : (arun k s arithmeticBody).regs rBad = 0) :
    let q := (s.regs rP + s.regs rNm2) / s.regs 237
    let p := s.regs rP + s.regs rGate * q
    s.regs rBad = 0 ∧ s.regs rP + s.regs rNm2 < M ∧ p < M ∧
      (arun k s arithmeticBody).regs rP = p ∧
      (s.regs rGate = 1 →
        p * 10000000 <
          (s.regs rOldL + 2 * rootTerm (s.regs rN) (s.regs rSqrt)) *
            17810724) ∧
      (arun k s arithmeticBody).regs rSqrt =
        sqrtNext (s.regs rN) (s.regs rSqrt) ∧
      (arun k s arithmeticBody).regs 237 = s.regs 237 + 1 ∧
      (arun k s arithmeticBody).regs rNm2 = s.regs rNm2 + 1 ∧
      (arun k s arithmeticBody).arr = s.arr := by
  dsimp only
  let d := arun k s productBody
  let e := arun k d rootTermBody
  let out := arun k e postGuardBody
  have hdword := arun_regs_word k productBody s hword harr
  have hdarr := arun_arr_word k productBody s hword harr
  have heword := arun_regs_word k rootTermBody d hdword hdarr
  have hearr := arun_arr_word k rootTermBody d hdword hdarr
  have hdSqrt : d.regs rSqrt = s.regs rSqrt :=
    aframe k rSqrt productBody s (by rfl)
  have hdN : d.regs rN = s.regs rN := aframe k rN productBody s (by rfl)
  have hdOld : d.regs rOldL = s.regs rOldL :=
    aframe k rOldL productBody s (by rfl)
  have hdDen : d.regs 237 = s.regs 237 := aframe k 237 productBody s (by rfl)
  have hdNm2 : d.regs rNm2 = s.regs rNm2 :=
    aframe k rNm2 productBody s (by rfl)
  have hdGate : d.regs rGate = s.regs rGate :=
    aframe k rGate productBody s (by rfl)
  have hd235 : d.regs 235 = s.regs 235 := aframe k 235 productBody s (by rfl)
  have hd236 : d.regs 236 = s.regs 236 := aframe k 236 productBody s (by rfl)
  have heSqrt : e.regs rSqrt = s.regs rSqrt :=
    (aframe k rSqrt rootTermBody d (by rfl)).trans hdSqrt
  have heN : e.regs rN = s.regs rN :=
    (aframe k rN rootTermBody d (by rfl)).trans hdN
  have heOld : e.regs rOldL = s.regs rOldL :=
    (aframe k rOldL rootTermBody d (by rfl)).trans hdOld
  have heDen : e.regs 237 = s.regs 237 :=
    (aframe k 237 rootTermBody d (by rfl)).trans hdDen
  have heNm2 : e.regs rNm2 = s.regs rNm2 :=
    (aframe k rNm2 rootTermBody d (by rfl)).trans hdNm2
  have heGate : e.regs rGate = s.regs rGate :=
    (aframe k rGate rootTermBody d (by rfl)).trans hdGate
  have he235 : e.regs 235 = s.regs 235 :=
    (aframe k 235 rootTermBody d (by rfl)).trans hd235
  have he236 : e.regs 236 = s.regs 236 :=
    (aframe k 236 rootTermBody d (by rfl)).trans hd236
  have hout : arun k s arithmeticBody = out := by
    simp only [arithmeticBody, arun_append, d, e, out]
  have houtZero : out.regs rBad = 0 := by rw [← hout]; exact hzero
  have hpst := postGuardBody_zero_sound k e
    (by rw [he235]; exact hcL) (by rw [he236]; exact hcR)
    (by rw [heSqrt]; exact hs1) (by rw [heSqrt]; exact hs1sq)
    (by rw [heN]; exact hn1) (by rw [heDen]; exact hden)
    (by rw [heNm2]; exact hnm2) heword hearr houtZero
  have heBad : e.regs rBad = 0 := hpst.1
  have hr := rootTermBody_zero_sound k d
    (by rw [hdSqrt]; exact hsq) (by rw [hdSqrt]; exact hs1)
    (by rw [hdSqrt]; exact hspos) (by rw [hdOld]; exact hOld)
    hdword hdarr heBad
  change d.regs rBad = 0 ∧
      ceilRootOf (d.regs rN) (d.regs rSqrt) ≠ 0 ∧
      2 * (RS62.fpD / ceilRootOf (d.regs rN) (d.regs rSqrt)) < M ∧
      d.regs rOldL +
          2 * (RS62.fpD / ceilRootOf (d.regs rN) (d.regs rSqrt)) < M ∧
      e.regs rRhsBase = d.regs rOldL +
          2 * (RS62.fpD / ceilRootOf (d.regs rN) (d.regs rSqrt)) ∧
      e.arr = d.arr at hr
  have hdBad : d.regs rBad = 0 := hr.1
  have hp := productBody_zero_sound k s hP hnm2W hGate hdenNe
    hword harr hdBad
  have hePNext : e.regs rPNext = d.regs rPNext :=
    aframe k rPNext rootTermBody d (by rfl)
  have hpGuard := hpst.2.1
  have hguard : s.regs rGate = 1 →
      (s.regs rP + s.regs rGate *
          ((s.regs rP + s.regs rNm2) / s.regs 237)) * 10000000 <
        (s.regs rOldL + 2 * rootTerm (s.regs rN) (s.regs rSqrt)) *
          17810724 := by
    intro hgate
    have hg := hpGuard (by rw [heGate]; exact hgate)
    rw [hePNext, hp.2.2.2.1, hr.2.2.2.2.1,
      hdOld, hdN, hdSqrt] at hg
    exact hg
  refine ⟨hp.1, hp.2.1, hp.2.2.1, ?_, hguard, ?_, ?_, ?_, ?_⟩
  · rw [hout, hpst.2.2.1, hePNext, hp.2.2.2.1]
  · rw [hout]
    simpa only [heN, heSqrt] using hpst.2.2.2.1
  · rw [hout]
    simpa only [heDen] using hpst.2.2.2.2.1
  · rw [hout]
    simpa only [heNm2] using hpst.2.2.2.2.2.1
  · rw [hout, hpst.2.2.2.2.2.2, hr.2.2.2.2.2, hp.2.2.2.2]

theorem loopBody_zero_sound (n0 k : Nat) (s : AState)
    (hkM : k < M) (hn2 : 2 ≤ n0 + k) (hn40 : n0 + k ≤ 2 ^ 40)
    (hnM : n0 + k < M) (hn1 : n0 + k + 1 < M)
    (hGate : s.arr k ≤ 1)
    (hOverflow : s.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1)
    (hP : s.regs rP < M) (hnm2W : s.regs rNm2 < M)
    (hdenNe : s.regs 237 ≠ 0)
    (hsq : s.regs rSqrt * s.regs rSqrt < M)
    (hs1 : s.regs rSqrt + 1 < M) (hspos : 0 < s.regs rSqrt)
    (hs1sq : (s.regs rSqrt + 1) * (s.regs rSqrt + 1) < M)
    (hden : s.regs 237 + 1 < M) (hnm2 : s.regs rNm2 + 1 < M)
    (hcL : s.regs 235 = 10000000) (hcR : s.regs 236 = 17810724)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hzero : (arun k s (body n0)).regs rBad = 0) :
    let q := (s.regs rP + s.regs rNm2) / s.regs 237
    let p := s.regs rP + s.arr k * q
    s.regs rBad = 0 ∧
      s.regs RS62PrimeMaskLadderOverflow.rBad = 0 ∧
      (arun k s (body n0)).regs rLogL =
        s.regs rLogL + RS62.incLWord (n0 + k) ∧
      (arun k s (body n0)).regs rLogU =
        s.regs rLogU + RS62.incUWord (n0 + k) ∧
      s.regs rP + s.regs rNm2 < M ∧ p < M ∧
      (arun k s (body n0)).regs rP = p ∧
      (s.arr k = 1 →
        p * 10000000 <
          (s.regs rLogL + 2 * rootTerm (n0 + k) (s.regs rSqrt)) *
            17810724) ∧
      (arun k s (body n0)).regs rSqrt =
        sqrtNext (n0 + k) (s.regs rSqrt) ∧
      (arun k s (body n0)).regs 237 = s.regs 237 + 1 ∧
      (arun k s (body n0)).regs rNm2 = s.regs rNm2 + 1 ∧
      (arun k s (body n0)).arr = s.arr := by
  dsimp only
  let a := arun k s snapshotBody
  let b := arun k a (ungatedLogBody (n0 + 1))
  let c := arun k b logBadBody
  let out := arun k c arithmeticBody
  have haword := arun_regs_word k snapshotBody s hword harr
  have haarr := arun_arr_word k snapshotBody s hword harr
  have hbword := arun_regs_word k
    (ungatedLogBody (n0 + 1)) a haword haarr
  have hbarr := arun_arr_word k
    (ungatedLogBody (n0 + 1)) a haword haarr
  have hcword := arun_regs_word k logBadBody b hbword hbarr
  have hcarr := arun_arr_word k logBadBody b hbword hbarr
  have hsnap := snapshotBody_run k s
  change a.regs rOldL = s.regs rLogL ∧ a.regs rBad = s.regs rBad ∧
    a.arr = s.arr at hsnap
  have haP : a.regs rP = s.regs rP := aframe k rP snapshotBody s (by rfl)
  have haSqrt : a.regs rSqrt = s.regs rSqrt :=
    aframe k rSqrt snapshotBody s (by rfl)
  have haDen : a.regs 237 = s.regs 237 := aframe k 237 snapshotBody s (by rfl)
  have haNm2 : a.regs rNm2 = s.regs rNm2 :=
    aframe k rNm2 snapshotBody s (by rfl)
  have ha235 : a.regs 235 = s.regs 235 := aframe k 235 snapshotBody s (by rfl)
  have ha236 : a.regs 236 = s.regs 236 := aframe k 236 snapshotBody s (by rfl)
  have haOverflow : a.regs RS62PrimeMaskLadderOverflow.rBad =
      s.regs RS62PrimeMaskLadderOverflow.rBad :=
    aframe k RS62PrimeMaskLadderOverflow.rBad snapshotBody s (by rfl)
  have haLogL : a.regs rLogL = s.regs rLogL :=
    aframe k rLogL snapshotBody s (by rfl)
  have haLogU : a.regs rLogU = s.regs rLogU :=
    aframe k rLogU snapshotBody s (by rfl)
  have hbst := ungatedLogBody_static (n0 + 1) k a hkM
    (by simpa only [Nat.add_sub_cancel] using hnM)
    (by rw [haOverflow]; exact hOverflow)
  change b.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1 ∧
    a.regs RS62PrimeMaskLadderOverflow.rBad ≤
      b.regs RS62PrimeMaskLadderOverflow.rBad ∧
    b.regs rGate = a.arr k ∧ b.regs rN = n0 + 1 - 1 + k ∧
    b.arr = a.arr at hbst
  have hbn := hbst.2.2
  have hbP : b.regs rP = s.regs rP :=
    (aframe k rP _ a (by rfl)).trans haP
  have hbSqrt : b.regs rSqrt = s.regs rSqrt :=
    (aframe k rSqrt _ a (by rfl)).trans haSqrt
  have hbDen : b.regs 237 = s.regs 237 :=
    (aframe k 237 _ a (by rfl)).trans haDen
  have hbNm2 : b.regs rNm2 = s.regs rNm2 :=
    (aframe k rNm2 _ a (by rfl)).trans haNm2
  have hbOld : b.regs rOldL = s.regs rLogL :=
    (aframe k rOldL _ a (by rfl)).trans hsnap.1
  have hb235 : b.regs 235 = s.regs 235 :=
    (aframe k 235 _ a (by rfl)).trans ha235
  have hb236 : b.regs 236 = s.regs 236 :=
    (aframe k 236 _ a (by rfl)).trans ha236
  have hcP : c.regs rP = s.regs rP :=
    (aframe k rP logBadBody b (by rfl)).trans hbP
  have hcSqrt : c.regs rSqrt = s.regs rSqrt :=
    (aframe k rSqrt logBadBody b (by rfl)).trans hbSqrt
  have hcDen : c.regs 237 = s.regs 237 :=
    (aframe k 237 logBadBody b (by rfl)).trans hbDen
  have hcNm2 : c.regs rNm2 = s.regs rNm2 :=
    (aframe k rNm2 logBadBody b (by rfl)).trans hbNm2
  have hcOld : c.regs rOldL = s.regs rLogL :=
    (aframe k rOldL logBadBody b (by rfl)).trans hbOld
  have hc235v : c.regs 235 = s.regs 235 :=
    (aframe k 235 logBadBody b (by rfl)).trans hb235
  have hc236v : c.regs 236 = s.regs 236 :=
    (aframe k 236 logBadBody b (by rfl)).trans hb236
  have hcGate : c.regs rGate = s.arr k := by
    rw [aframe k rGate logBadBody b (by rfl), hbn.1, hsnap.2.2]
  have hcN : c.regs rN = n0 + k := by
    rw [aframe k rN logBadBody b (by rfl), hbn.2.1]
    omega
  have hout : arun k s (body n0) = out := by
    simp only [body, arun_append, a, b, c, out]
  have houtZero : out.regs rBad = 0 := by rw [← hout]; exact hzero
  have harith := arithmeticBody_zero_sound k c
    (by rw [hcP]; exact hP) (by rw [hcNm2]; exact hnm2W)
    (by rw [hcGate]; exact hGate) (by rw [hcDen]; exact hdenNe)
    (by rw [hcSqrt]; exact hsq) (by rw [hcSqrt]; exact hs1)
    (by rw [hcSqrt]; exact hspos) (by rw [hcSqrt]; exact hs1sq)
    (by rw [hcN]; exact hn1) (by rw [hcOld]; exact hword rLogL)
    (by rw [hcDen]; exact hden) (by rw [hcNm2]; exact hnm2)
    (by rw [hc235v]; exact hcL) (by rw [hc236v]; exact hcR)
    hcword hcarr houtZero
  have hlog := logBadBody_run k b hbword
  change c.regs rBad =
      (b.regs rBad ||| b.regs RS62PrimeMaskLadderOverflow.rBad) ∧
    c.arr = b.arr at hlog
  have hzOr : b.regs rBad ||| b.regs RS62PrimeMaskLadderOverflow.rBad = 0 :=
    hlog.1.symm.trans harith.1
  have hbBad : b.regs rBad = 0 := bor_eq_zero_left hzOr
  have hbOverflow : b.regs RS62PrimeMaskLadderOverflow.rBad = 0 :=
    bor_eq_zero_right hzOr
  have hbOwn : b.regs rBad = s.regs rBad :=
    (aframe k rBad (ungatedLogBody (n0 + 1)) a
      (by rfl)).trans hsnap.2.1
  have hover := ungatedLogBody_zero_sound (n0 + 1) k a
    hkM (by simpa only [Nat.add_sub_cancel] using hn2)
    (by simpa only [Nat.add_sub_cancel] using hn40)
    (by simpa only [Nat.add_sub_cancel] using hnM)
    (by rw [haLogL]; exact hword rLogL)
    (by rw [haLogU]; exact hword rLogU)
    (by rw [haOverflow]; exact hOverflow) hbOverflow
  have hcLogL : c.regs rLogL = b.regs rLogL :=
    aframe k rLogL logBadBody b (by rfl)
  have hcLogU : c.regs rLogU = b.regs rLogU :=
    aframe k rLogU logBadBody b (by rfl)
  have outLogL : out.regs rLogL = c.regs rLogL :=
    aframe k rLogL arithmeticBody c (by rfl)
  have outLogU : out.regs rLogU = c.regs rLogU :=
    aframe k rLogU arithmeticBody c (by rfl)
  have hguard : s.arr k = 1 →
      (s.regs rP + s.arr k *
          ((s.regs rP + s.regs rNm2) / s.regs 237)) * 10000000 <
        (s.regs rLogL + 2 * rootTerm (n0 + k) (s.regs rSqrt)) *
          17810724 := by
    intro hg
    have := harith.2.2.2.2.1 (by rw [hcGate]; exact hg)
    simpa only [hcP, hcNm2, hcDen, hcGate, hcOld, hcN, hcSqrt] using this
  have hsum : s.regs rP + s.regs rNm2 < M := by
    simpa only [hcP, hcNm2] using harith.2.1
  have hpBound : s.regs rP + s.arr k *
      ((s.regs rP + s.regs rNm2) / s.regs 237) < M := by
    simpa only [hcP, hcGate, hcNm2, hcDen] using harith.2.2.1
  refine ⟨?_, ?_, ?_, ?_, hsum, hpBound, ?_, hguard,
    ?_, ?_, ?_, ?_⟩
  · rw [← hbOwn]
    exact hbBad
  · rw [← haOverflow]
    exact hover.1
  · rw [hout, outLogL, hcLogL, hover.2.2.2.1, haLogL]
    simp only [Nat.add_sub_cancel]
  · rw [hout, outLogU, hcLogU, hover.2.2.2.2.1, haLogU]
    simp only [Nat.add_sub_cancel]
  · rw [hout]
    simpa only [hcP, hcGate, hcNm2, hcDen] using harith.2.2.2.1
  · rw [hout]
    simpa only [hcN, hcSqrt] using harith.2.2.2.2.2.1
  · rw [hout]
    simpa only [hcDen] using harith.2.2.2.2.2.2.1
  · rw [hout]
    simpa only [hcNm2] using harith.2.2.2.2.2.2.2.1
  · rw [hout, harith.2.2.2.2.2.2.2.2, hlog.2,
      hover.2.2.2.2.2.2.2, hsnap.2.2]

theorem loopBody_static (n0 k : Nat) (s : AState)
    (hkM : k < M) (hnM : n0 + k < M)
    (hOverflow : s.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1)
    (hs1 : s.regs rSqrt + 1 < M)
    (hs1sq : (s.regs rSqrt + 1) * (s.regs rSqrt + 1) < M)
    (hn1 : n0 + k + 1 < M)
    (hden : s.regs 237 + 1 < M) (hnm2 : s.regs rNm2 + 1 < M)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M) :
    let out := arun k s (body n0)
    out.regs rSqrt = sqrtNext (n0 + k) (s.regs rSqrt) ∧
      out.regs 237 = s.regs 237 + 1 ∧
      out.regs rNm2 = s.regs rNm2 + 1 ∧
      out.regs 235 = s.regs 235 ∧ out.regs 236 = s.regs 236 ∧
      out.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1 ∧ out.arr = s.arr := by
  let a := arun k s snapshotBody
  let b := arun k a (ungatedLogBody (n0 + 1))
  let pre := arun k b afterOverflowBody
  let g := arun k pre sqrtAdvanceBody
  let out := arun k g denominatorAdvanceBody
  have haword := arun_regs_word k snapshotBody s hword harr
  have haarr := arun_arr_word k snapshotBody s hword harr
  have hbword := arun_regs_word k
    (ungatedLogBody (n0 + 1)) a haword haarr
  have hbarr := arun_arr_word k
    (ungatedLogBody (n0 + 1)) a haword haarr
  have hpword := arun_regs_word k afterOverflowBody b hbword hbarr
  have hparr := arun_arr_word k afterOverflowBody b hbword hbarr
  have hgword := arun_regs_word k sqrtAdvanceBody pre hpword hparr
  have haOverflow : a.regs RS62PrimeMaskLadderOverflow.rBad =
      s.regs RS62PrimeMaskLadderOverflow.rBad :=
    aframe k RS62PrimeMaskLadderOverflow.rBad snapshotBody s (by rfl)
  have hbst := ungatedLogBody_static (n0 + 1) k a hkM
    (by simpa only [Nat.add_sub_cancel] using hnM)
    (by rw [haOverflow]; exact hOverflow)
  change b.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1 ∧
    a.regs RS62PrimeMaskLadderOverflow.rBad ≤
      b.regs RS62PrimeMaskLadderOverflow.rBad ∧
    b.regs rGate = a.arr k ∧ b.regs rN = n0 + 1 - 1 + k ∧
    b.arr = a.arr at hbst
  have hmono := hbst.1
  have hbn := hbst.2.2
  have hpSqrt : pre.regs rSqrt = s.regs rSqrt :=
    (aframe k rSqrt afterOverflowBody b (by rfl)).trans
      ((aframe k rSqrt _ a (by rfl)).trans
        (aframe k rSqrt snapshotBody s (by rfl)))
  have hpN : pre.regs rN = n0 + k := by
    rw [aframe k rN afterOverflowBody b (by rfl), hbn.2.1]
    omega
  have hpDen : pre.regs 237 = s.regs 237 :=
    (aframe k 237 afterOverflowBody b (by rfl)).trans
      ((aframe k 237 _ a (by rfl)).trans
        (aframe k 237 snapshotBody s (by rfl)))
  have hpNm2 : pre.regs rNm2 = s.regs rNm2 :=
    (aframe k rNm2 afterOverflowBody b (by rfl)).trans
      ((aframe k rNm2 _ a (by rfl)).trans
        (aframe k rNm2 snapshotBody s (by rfl)))
  have hp235 : pre.regs 235 = s.regs 235 :=
    (aframe k 235 afterOverflowBody b (by rfl)).trans
      ((aframe k 235 _ a (by rfl)).trans
        (aframe k 235 snapshotBody s (by rfl)))
  have hp236 : pre.regs 236 = s.regs 236 :=
    (aframe k 236 afterOverflowBody b (by rfl)).trans
      ((aframe k 236 _ a (by rfl)).trans
        (aframe k 236 snapshotBody s (by rfl)))
  have hpOverflow : pre.regs RS62PrimeMaskLadderOverflow.rBad =
      b.regs RS62PrimeMaskLadderOverflow.rBad :=
    aframe k RS62PrimeMaskLadderOverflow.rBad afterOverflowBody b (by rfl)
  have hsqrt := sqrtAdvanceBody_run k pre
    (by rw [hpSqrt]; exact hs1) (by rw [hpSqrt]; exact hs1sq)
    (by rw [hpN]; exact hn1)
  change g.regs rSqrt = sqrtNext (pre.regs rN) (pre.regs rSqrt) ∧
    g.arr = pre.arr at hsqrt
  have hgDen : g.regs 237 = s.regs 237 :=
    (aframe k 237 sqrtAdvanceBody pre (by rfl)).trans hpDen
  have hgNm2 : g.regs rNm2 = s.regs rNm2 :=
    (aframe k rNm2 sqrtAdvanceBody pre (by rfl)).trans hpNm2
  have hdenRun := denominatorAdvanceBody_run k g
    (by rw [hgDen]; exact hden) (by rw [hgNm2]; exact hnm2)
  change out.regs 237 = g.regs 237 + 1 ∧
    out.regs rNm2 = g.regs rNm2 + 1 ∧ out.arr = g.arr at hdenRun
  have hg235 : g.regs 235 = s.regs 235 :=
    (aframe k 235 sqrtAdvanceBody pre (by rfl)).trans hp235
  have hg236 : g.regs 236 = s.regs 236 :=
    (aframe k 236 sqrtAdvanceBody pre (by rfl)).trans hp236
  have ho235 : out.regs 235 = g.regs 235 :=
    aframe k 235 denominatorAdvanceBody g (by rfl)
  have ho236 : out.regs 236 = g.regs 236 :=
    aframe k 236 denominatorAdvanceBody g (by rfl)
  have hgOverflow : g.regs RS62PrimeMaskLadderOverflow.rBad =
      pre.regs RS62PrimeMaskLadderOverflow.rBad :=
    aframe k RS62PrimeMaskLadderOverflow.rBad sqrtAdvanceBody pre (by rfl)
  have hoOverflow : out.regs RS62PrimeMaskLadderOverflow.rBad =
      g.regs RS62PrimeMaskLadderOverflow.rBad :=
    aframe k RS62PrimeMaskLadderOverflow.rBad denominatorAdvanceBody g (by rfl)
  have hoSqrt : out.regs rSqrt = g.regs rSqrt :=
    aframe k rSqrt denominatorAdvanceBody g (by rfl)
  have hout : arun k s (body n0) = out := by
    rw [body_eq_preSqrt]
    simp only [preSqrtBody, arun_append, a, b, pre, g, out]
  have hsnapArr : a.arr = s.arr := (snapshotBody_run k s).2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hout, hoSqrt, hsqrt.1, hpN, hpSqrt]
  · rw [hout, hdenRun.1, hgDen]
  · rw [hout, hdenRun.2.1, hgNm2]
  · rw [hout, ho235, hg235]
  · rw [hout, ho236, hg236]
  · rw [hout, hoOverflow, hgOverflow, hpOverflow]
    exact hmono
  · rw [hout, hdenRun.2.2, hsqrt.2]
    have hpArr : pre.arr = b.arr := by
      dsimp only [pre]
      exact LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
        k afterOverflowBody b (by rfl)
    rw [hpArr, hbn.2.2, hsnapArr]

def machineFoldState (arr : Nat → Nat)
    (n0 f SL P sqrt0 den0 nm20 : Nat) : AState :=
  (List.range f).foldl (fun st k => arun k st (body n0))
    (arun 0 (initialAStateWithArray arr) (init SL P sqrt0 den0 nm20))

theorem machineFoldState_succ (arr : Nat → Nat)
    (n0 f SL P sqrt0 den0 nm20 : Nat) :
    machineFoldState arr n0 (f + 1) SL P sqrt0 den0 nm20 =
      arun f (machineFoldState arr n0 f SL P sqrt0 den0 nm20) (body n0) := by
  unfold machineFoldState
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem init_spec (arr : Nat → Nat) (SL P sqrt0 den0 nm20 : Nat)
    (hSL : SL < M) (hP : P < M) (hsqrt : sqrt0 < M)
    (hden : den0 < M) (hnm2 : nm20 < M) :
    let out := arun 0 (initialAStateWithArray arr)
      (init SL P sqrt0 den0 nm20)
    out.regs rLogL = SL ∧ out.regs rLogU = SL ∧ out.regs rP = P ∧
      out.regs rSqrt = sqrt0 ∧ out.regs 237 = den0 ∧
      out.regs rNm2 = nm20 ∧ out.regs rBad = 0 ∧
      out.regs RS62PrimeMaskLadderOverflow.rBad = 0 ∧
      out.regs 235 = 10000000 ∧ out.regs 236 = 17810724 ∧
      out.arr = arr := by
  simp [init, RS62PrimeMaskLadder.init, constantsBody, arun, astep,
    initialAStateWithArray, AState.writeReg, sdest, sval, denoteOperand,
    rLogL, rLogU, rP, rSqrt, rNm2, rBad,
    RS62PrimeMaskLadder.rLogL, RS62PrimeMaskLadder.rLogU,
    RamareCombined100M.LogSweep.rLogL,
    RamareCombined100M.LogSweep.rLogU,
    RS62PrimeMaskLadderOverflow.rBad,
    Nat.mod_eq_of_lt hSL, Nat.mod_eq_of_lt hP,
    Nat.mod_eq_of_lt hsqrt, Nat.mod_eq_of_lt hden,
    Nat.mod_eq_of_lt hnm2, M]
  exact ⟨by simpa only [M] using hSL, by simpa only [M] using hP,
    by simpa only [M] using hsqrt, by simpa only [M] using hden,
    by simpa only [M] using hnm2⟩

theorem machineFold_word (arr : Nat → Nat)
    (n0 f SL P sqrt0 den0 nm20 : Nat) (harray : ∀ j, arr j < M) :
    (∀ j, (machineFoldState arr n0 f SL P sqrt0 den0 nm20).regs j < M) ∧
      ∀ j, (machineFoldState arr n0 f SL P sqrt0 den0 nm20).arr j < M := by
  induction f with
  | zero =>
      unfold machineFoldState
      simp only [List.range_zero, List.foldl_nil]
      exact arun_word 0 (init SL P sqrt0 den0 nm20)
        (initialAStateWithArray arr) (by
          intro j
          simp [initialAStateWithArray, Reflect.initialState, M]) (by
          simpa [initialAStateWithArray] using harray)
  | succ f ih =>
      rw [machineFoldState_succ]
      exact arun_word f (body n0)
        (machineFoldState arr n0 f SL P sqrt0 den0 nm20) ih.1 ih.2

theorem sqrtNext_sqrt (n : Nat) : sqrtNext n (Nat.sqrt n) = Nat.sqrt (n + 1) := by
  unfold sqrtNext
  by_cases h : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ n + 1
  · simp only [h, if_true]
    apply LeanCompCert.Verified.SqrtEquiv.sqrt_unique
    · exact h
    · have hs : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) :=
        Nat.lt_succ_sqrt n
      have hlt : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) <
          (Nat.sqrt n + 2) * (Nat.sqrt n + 2) :=
        Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega)
      have hres : n + 1 < (Nat.sqrt n + 2) * (Nat.sqrt n + 2) := by
        exact Nat.lt_of_le_of_lt (by omega) hlt
      have heq : Nat.sqrt n + 2 = Nat.sqrt n + 1 + 1 := by omega
      rw [← heq]
      exact hres
  · simp only [h, if_false, Nat.add_zero]
    apply LeanCompCert.Verified.SqrtEquiv.sqrt_unique
    · exact Nat.le_trans (Nat.sqrt_le n) (by omega)
    · omega

private theorem sqrt_production_bounds {n : Nat} (hn1 : 1 ≤ n)
    (hn : n ≤ 100000001) :
    0 < Nat.sqrt n ∧ Nat.sqrt n * Nat.sqrt n < M ∧
      Nat.sqrt n + 1 < M ∧
      (Nat.sqrt n + 1) * (Nat.sqrt n + 1) < M := by
  have hsle : Nat.sqrt n ≤ 10000 := by
    by_cases h : Nat.sqrt n ≤ 10000
    · exact h
    · have h10001 : 10001 ≤ Nat.sqrt n := by omega
      have hmul : 10001 * 10001 ≤ Nat.sqrt n * Nat.sqrt n :=
        Nat.mul_le_mul h10001 h10001
      have hs := Nat.sqrt_le n
      omega
  have hspos : 0 < Nat.sqrt n := by
    have hs := Nat.lt_succ_sqrt n
    by_cases h : Nat.sqrt n = 0
    · simp [h] at hs
      omega
    · omega
  have hsquare := Nat.sqrt_le n
  have hnext : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ 10001 * 10001 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hsmall : 10001 * 10001 < M := by decide
  exact ⟨hspos, Nat.lt_of_le_of_lt hsquare (by omega), by omega,
    Nat.lt_of_le_of_lt hnext hsmall⟩

theorem machineFold_static (arr : Nat → Nat)
    (n0 f SL P sqrt0 den0 nm20 : Nat)
    (harray : ∀ j, arr j < M) (hn0 : 1 ≤ n0)
    (hEnd : n0 + f ≤ 100000001)
    (hdenEnd : den0 + f < M) (hnm2End : nm20 + f < M)
    (hSL : SL < M) (hP : P < M) (hsqrt0 : sqrt0 < M)
    (hden0 : den0 < M) (hnm20 : nm20 < M)
    (hsqrtInit : sqrt0 = Nat.sqrt n0) :
    let out := machineFoldState arr n0 f SL P sqrt0 den0 nm20
    out.regs rSqrt = Nat.sqrt (n0 + f) ∧
      out.regs 237 = den0 + f ∧ out.regs rNm2 = nm20 + f ∧
      out.regs 235 = 10000000 ∧ out.regs 236 = 17810724 ∧
      out.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1 ∧ out.arr = arr := by
  induction f with
  | zero =>
      have hi := init_spec arr SL P sqrt0 den0 nm20
        hSL hP hsqrt0 hden0 hnm20
      simp only [machineFoldState, List.range_zero, List.foldl_nil,
        Nat.add_zero]
      exact ⟨hi.2.2.2.1.trans hsqrtInit, hi.2.2.2.2.1,
        hi.2.2.2.2.2.1, hi.2.2.2.2.2.2.2.2.1,
        hi.2.2.2.2.2.2.2.2.2.1,
        by rw [hi.2.2.2.2.2.2.2.1]; omega,
        hi.2.2.2.2.2.2.2.2.2.2⟩
  | succ f ih =>
      let mid := machineFoldState arr n0 f SL P sqrt0 den0 nm20
      have hEnd' : n0 + f ≤ 100000001 := by omega
      have hdenEnd' : den0 + f < M := by omega
      have hnm2End' : nm20 + f < M := by omega
      have hm := ih hEnd' hdenEnd' hnm2End'
      change mid.regs rSqrt = Nat.sqrt (n0 + f) ∧
        mid.regs 237 = den0 + f ∧ mid.regs rNm2 = nm20 + f ∧
        mid.regs 235 = 10000000 ∧ mid.regs 236 = 17810724 ∧
        mid.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1 ∧ mid.arr = arr at hm
      have hmw := machineFold_word arr n0 f SL P sqrt0 den0 nm20 harray
      change (∀ j, mid.regs j < M) ∧ ∀ j, mid.arr j < M at hmw
      have hsb := sqrt_production_bounds (n := n0 + f) (by omega) hEnd'
      have hs := loopBody_static n0 f mid
        (Nat.lt_of_le_of_lt
          (Nat.le_trans (Nat.le_add_left f n0) hEnd') (by decide))
        (Nat.lt_of_le_of_lt hEnd' (by decide)) hm.2.2.2.2.2.1
        (by rw [hm.1]; exact hsb.2.2.1)
        (by rw [hm.1]; exact hsb.2.2.2)
        (by
          apply Nat.lt_of_le_of_lt (show n0 + f + 1 ≤ 100000001 by omega)
          decide)
        (by rw [hm.2.1]; exact hdenEnd)
        (by rw [hm.2.2.1]; exact hnm2End)
        hmw.1 hmw.2
      have hsqrtStep : sqrtNext (n0 + f) (mid.regs rSqrt) =
          Nat.sqrt (n0 + (f + 1)) := by
        rw [hm.1, sqrtNext_sqrt]
        congr 1
      rw [machineFoldState_succ]
      exact ⟨hs.1.trans hsqrtStep,
        hs.2.1.trans (by rw [hm.2.1]; omega),
        hs.2.2.1.trans (by rw [hm.2.2.1]; omega),
        hs.2.2.2.1.trans hm.2.2.2.1,
        hs.2.2.2.2.1.trans hm.2.2.2.2.1,
        hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.trans hm.2.2.2.2.2.2⟩

def CellGuards (arr : Nat → Nat) (n0 f : Nat) (initial : State410) : Prop :=
  ∀ k, k < f →
    let st := sourceFold arr n0 k initial
    arr k = 0 ∨ guardStrong (n0 + k) st.logL
      (productCandidate (arr k) (n0 + k) st.product) st.sqrt

theorem machineFold_clean_observe (arr : Nat → Nat)
    (n0 f SL P sqrt0 den0 nm20 : Nat)
    (harray : ∀ j, arr j < M) (hcells : ∀ k, k < f → arr k ≤ 1)
    (hn0 : 2 ≤ n0) (hfM : f < M) (hEnd : n0 + f ≤ 100000001)
    (hSL : SL < M) (hP : P < M) (hsqrt0 : sqrt0 < M)
    (hden0 : den0 < M) (hnm20 : nm20 < M)
    (hsqrtInit : sqrt0 = Nat.sqrt n0)
    (hdenInit : den0 = n0 - 1) (hnm2Init : nm20 = n0 - 2)
    (hClean :
      (machineFoldState arr n0 f SL P sqrt0 den0 nm20).regs rBad = 0) :
    let initial : State410 := ⟨SL, SL, P, sqrt0, 0⟩
    let out := machineFoldState arr n0 f SL P sqrt0 den0 nm20
    let src := sourceFold arr n0 f initial
    out.regs rLogL = src.logL ∧ out.regs rLogU = src.logU ∧
      out.regs rP = src.product ∧ out.regs rSqrt = src.sqrt ∧
      out.arr = arr ∧ src.bad = 0 ∧ CellGuards arr n0 f initial := by
  induction f with
  | zero =>
      have hi := init_spec arr SL P sqrt0 den0 nm20
        hSL hP hsqrt0 hden0 hnm20
      simp only [machineFoldState, List.range_zero, List.foldl_nil,
        sourceFold, State410.logL, State410.logU, State410.product,
        State410.sqrt, State410.bad]
      refine ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1,
        hi.2.2.2.2.2.2.2.2.2.2, trivial, ?_⟩
      intro k hk
      omega
  | succ f ih =>
      let initial : State410 := ⟨SL, SL, P, sqrt0, 0⟩
      let mid := machineFoldState arr n0 f SL P sqrt0 den0 nm20
      let src := sourceFold arr n0 f initial
      have hfM' : f < M := by omega
      have hEnd' : n0 + f ≤ 100000001 := by omega
      have hcells' : ∀ k, k < f → arr k ≤ 1 := fun k hk =>
        hcells k (Nat.lt_succ_of_lt hk)
      have hm := machineFold_static arr n0 f SL P sqrt0 den0 nm20
        harray (by omega) hEnd'
        (by
          rw [hdenInit]
          apply Nat.lt_of_le_of_lt (show n0 - 1 + f ≤ 100000001 by omega)
          decide)
        (by
          rw [hnm2Init]
          apply Nat.lt_of_le_of_lt (show n0 - 2 + f ≤ 100000001 by omega)
          decide)
        hSL hP hsqrt0 hden0 hnm20 hsqrtInit
      change mid.regs rSqrt = Nat.sqrt (n0 + f) ∧
        mid.regs 237 = den0 + f ∧ mid.regs rNm2 = nm20 + f ∧
        mid.regs 235 = 10000000 ∧ mid.regs 236 = 17810724 ∧
        mid.regs RS62PrimeMaskLadderOverflow.rBad ≤ 1 ∧ mid.arr = arr at hm
      have hmw := machineFold_word arr n0 f SL P sqrt0 den0 nm20 harray
      change (∀ j, mid.regs j < M) ∧ ∀ j, mid.arr j < M at hmw
      have hsb := sqrt_production_bounds (n := n0 + f) (by omega) hEnd'
      have hlastClean : (arun f mid (body n0)).regs rBad = 0 := by
        rw [← machineFoldState_succ]
        exact hClean
      have hlast := loopBody_zero_sound n0 f mid hfM'
        (by omega) (by omega)
        (Nat.lt_of_le_of_lt hEnd' (by decide))
        (Nat.lt_of_le_of_lt
          (show n0 + f + 1 ≤ 100000001 by omega) (by decide))
        (by rw [hm.2.2.2.2.2.2]; exact hcells f (Nat.lt_succ_self f))
        hm.2.2.2.2.2.1 (hmw.1 rP) (hmw.1 rNm2)
        (by rw [hm.2.1, hdenInit]; omega)
        (by rw [hm.1]; exact hsb.2.1)
        (by rw [hm.1]; exact hsb.2.2.1)
        (by rw [hm.1]; exact hsb.1)
        (by rw [hm.1]; exact hsb.2.2.2)
        (by
          rw [hm.2.1, hdenInit]
          apply Nat.lt_of_le_of_lt
            (show n0 - 1 + f + 1 ≤ 100000001 by omega)
          decide)
        (by
          rw [hm.2.2.1, hnm2Init]
          apply Nat.lt_of_le_of_lt
            (show n0 - 2 + f + 1 ≤ 100000001 by omega)
          decide)
        hm.2.2.2.1 hm.2.2.2.2.1 hmw.1 hmw.2 hlastClean
      rcases hlast with
        ⟨hmidBad, hmidOverflow, houtLogL, houtLogU, hNumerBound,
          hProductBound, houtProduct, hcellGuard, houtSqrt, houtDen,
          houtNm2, houtArr⟩
      have hprev := ih hcells' hfM' hEnd' hmidBad
      change mid.regs rLogL = src.logL ∧ mid.regs rLogU = src.logU ∧
        mid.regs rP = src.product ∧ mid.regs rSqrt = src.sqrt ∧
        mid.arr = arr ∧ src.bad = 0 ∧ CellGuards arr n0 f initial at hprev
      have hdenMid : mid.regs 237 = n0 + f - 1 := by
        rw [hm.2.1, hdenInit]
        omega
      have hnm2Mid : mid.regs rNm2 = n0 + f - 2 := by
        rw [hm.2.2.1, hnm2Init]
        omega
      have hprodForm :
          (mid.regs rP + mid.regs rNm2) / mid.regs 237 =
            (src.product + (n0 + f) - 2) / (n0 + f - 1) := by
        rw [hprev.2.2.1, hdenMid, hnm2Mid]
        rw [show src.product + (n0 + f - 2) =
            src.product + (n0 + f) - 2 by omega]
      have hstep : sourceStep arr n0 src f =
          { logL := src.logL + RS62.incLWord (n0 + f)
            logU := src.logU + RS62.incUWord (n0 + f)
            product := src.product + arr f *
              ((src.product + (n0 + f) - 2) / (n0 + f - 1))
            sqrt := sqrtNext (n0 + f) src.sqrt
            bad := 0 } := by
        unfold sourceStep productCandidate
        dsimp only
        rw [hprev.2.2.2.2.2.1]
        by_cases hcell0 : arr f = 0
        · simp [hcell0]
        · have hcell1 : arr f = 1 := by
            have := hcells f (Nat.lt_succ_self f)
            omega
          have hguard := hcellGuard
            (by rw [hm.2.2.2.2.2.2, hcell1])
          rw [hprodForm, hprev.1, hprev.2.2.1, hprev.2.2.2.1,
            hm.2.2.2.2.2.2, hcell1, Nat.one_mul] at hguard
          have hstrong : guardStrong (n0 + f) src.logL
              (src.product +
                (src.product + (n0 + f) - 2) / (n0 + f - 1)) src.sqrt := by
            unfold guardStrong
            simpa only [Nat.mul_comm] using hguard
          unfold guardStrong at hstrong
          simp only [hcell1, Nat.one_mul]
          rw [if_pos hstrong, Nat.or_zero]
      dsimp only
      rw [machineFoldState_succ, sourceFold_succ]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hstep]
        simpa only [mid, hprev.1, hm.2.2.2.2.2.2] using houtLogL
      · rw [hstep]
        simpa only [mid, hprev.2.1, hm.2.2.2.2.2.2] using houtLogU
      · rw [hstep]
        have hp' := houtProduct
        rw [hprodForm, hprev.2.2.1, hm.2.2.2.2.2.2] at hp'
        simpa only [mid] using hp'
      · rw [hstep]
        simpa only [mid, hprev.2.2.2.1] using houtSqrt
      · exact houtArr.trans hprev.2.2.2.2.1
      · rw [hstep]
      · intro k hk
        by_cases hkf : k < f
        · exact hprev.2.2.2.2.2.2 k hkf
        · have hkEq : k = f := by omega
          subst k
          have hcell := hcells f (Nat.lt_succ_self f)
          rcases (by omega : arr f = 0 ∨ arr f = 1) with h0 | h1
          · exact Or.inl h0
          · exact Or.inr (by
              have hg := hcellGuard (by
                rw [hm.2.2.2.2.2.2, h1])
              rw [hprodForm, hprev.1, hprev.2.2.1, hprev.2.2.2.1,
                hm.2.2.2.2.2.2, h1, Nat.one_mul] at hg
              unfold guardStrong
              unfold rootTerm at hg ⊢
              simp only [productCandidate, h1, Nat.one_mul]
              simpa only [Nat.mul_comm] using hg)

theorem sourceFold_of_runFromArray (arr : Nat → Nat)
    (n0 f SL P sqrt0 den0 nm20 outReg : Nat) (out : AState)
    (harray : ∀ j, arr j < M) (hcells : ∀ k, k < f → arr k ≤ 1)
    (hn0 : 2 ≤ n0) (hfM : f < M) (hEnd : n0 + f ≤ 100000001)
    (hSL : SL < M) (hP : P < M) (hsqrt0 : sqrt0 < M)
    (hden0 : den0 < M) (hnm20 : nm20 < M)
    (hsqrtInit : sqrt0 = Nat.sqrt n0)
    (hdenInit : den0 = n0 - 1) (hnm2Init : nm20 = n0 - 2)
    (hRun : (program n0 f SL P sqrt0 den0 nm20 outReg).runFromArray arr =
      some out)
    (hClean : out.regs rBad = 0) :
    let initial : State410 := ⟨SL, SL, P, sqrt0, 0⟩
    let src := sourceFold arr n0 f initial
    out.regs rLogL = src.logL ∧ out.regs rLogU = src.logU ∧
      out.regs rP = src.product ∧ out.regs rSqrt = src.sqrt ∧
      out.arr = arr ∧ src.bad = 0 ∧ CellGuards arr n0 f initial := by
  let mid := machineFoldState arr n0 f SL P sqrt0 den0 nm20
  have hout := AProgram.eq_arun_of_runFromArray_eq_some
    (program n0 f SL P sqrt0 den0 nm20 outReg) arr out hRun
  have houtEq : out = mid := by
    simpa [program, machineFoldState, mid, arun] using hout
  have hmidClean : mid.regs rBad = 0 := by rw [← houtEq]; exact hClean
  have hobs := machineFold_clean_observe arr n0 f SL P sqrt0 den0 nm20
    harray hcells hn0 hfM hEnd hSL hP hsqrt0 hden0 hnm20
    hsqrtInit hdenInit hnm2Init hmidClean
  simpa only [houtEq] using hobs

end LeanCompCert.Ports.RS62Loop410Sound
