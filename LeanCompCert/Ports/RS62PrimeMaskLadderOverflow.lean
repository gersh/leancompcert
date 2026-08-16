import LeanCompCert.Ports.RS62PrimeMaskLadder

/-!
# Compiled no-wrap checker for the RS62 prime-mask ladder

The useful RS62 increments occur only at prime-mask cells.  A worst-case
`segmentLength * 2^48` bound is therefore both wasteful and false at the
production segment sizes.  This program executes the actual mask-gated
ladder and latches a failure whenever either unsigned endpoint addition
wraps.  A later generic refinement theorem turns a zero latch into the
prefix `Room` property; no checkpoint fold is evaluated in Lean.
-/

namespace LeanCompCert.Ports.RS62PrimeMaskLadderOverflow

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.RS62 (incLWord incUWord fpD)
open LeanCompCert.Ports.RamareCombined100M.LogSweep

def rOldL : Nat := 200
def rOldU : Nat := 201
def rWrapL : Nat := 202
def rWrapU : Nat := 203
def rWrap : Nat := 204
def rBad : Nat := 205
def regCount : Nat := 206

/-- Preserve the old endpoints, execute the exact ladder step, then latch
either unsigned-addition wrap bit. -/
def saveBody : List AInstr :=
  [ .scalar (.mov rOldL (.reg rLogL))
  , .scalar (.mov rOldU (.reg rLogU)) ]

def checkBody : List AInstr :=
  [ .scalar (.binop rWrapL .lt (.reg rLogL) (.reg rOldL))
  , .scalar (.binop rWrapU .lt (.reg rLogU) (.reg rOldU))
  , .scalar (.binop rWrap .bor (.reg rWrapL) (.reg rWrapU))
  , .scalar (.binop rBad .bor (.reg rBad) (.reg rWrap)) ]

def body (n0 : Nat) : List AInstr :=
  saveBody ++ RS62PrimeMaskLadder.body n0 ++ checkBody

def program (n0 f SL SU : Nat) (outReg : Nat := rBad) : AProgram := {
  regCount := regCount
  arrayLen := f
  loopCount := f
  init := RS62PrimeMaskLadder.init SL SU ++
    [AInstr.scalar (.mov rBad (.lit 0))]
  body := body n0
  epilogue := []
  output := outReg
}

set_option maxRecDepth 40000 in
theorem body_all (n0 : Nat) :
    (body n0).all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 40000 in
theorem init_all (SL SU : Nat) :
    (RS62PrimeMaskLadder.init SL SU ++
      [AInstr.scalar (.mov rBad (.lit 0))]).all (ainstrWFB regCount) = true := by
  rfl

theorem program_wf (n0 f SL SU outReg : Nat) (hout : outReg < regCount) :
    (program n0 f SL SU outReg).WF :=
  ⟨hout, forall_wf_of_all (init_all SL SU),
    forall_wf_of_all (body_all n0), by simp [program]⟩

/-! ## Symbolic meaning of one checked step -/

private theorem commitLowerAddBody_run_mod (k : Nat) (s : AState) :
    (arun k s (lift commitLowerAddBody)).regs rLogL =
      (s.regs rLogL + s.regs rA) % M := by
  rw [arun_lift]
  simp [commitLowerAddBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rLogL, rA]

private theorem commitUpperAddBody_run_mod (k : Nat) (s : AState) :
    (arun k s (lift commitUpperAddBody)).regs rLogU =
      (s.regs rLogU + s.regs rB) % M := by
  rw [arun_lift]
  simp [commitUpperAddBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rLogU, rB]

theorem saveBody_run (k : Nat) (s : AState) :
    let out := arun k s saveBody
    out.regs rOldL = s.regs rLogL ∧
      out.regs rOldU = s.regs rLogU ∧
      out.regs rLogL = s.regs rLogL ∧
      out.regs rLogU = s.regs rLogU ∧
      out.regs rBad = s.regs rBad ∧ out.arr = s.arr := by
  simp [saveBody, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, rOldL, rOldU, rBad, rLogL, rLogU]

theorem checkBody_run (k : Nat) (s : AState)
    (hbad : s.regs 205 ≤ 1) :
    let out := arun k s checkBody
    out.regs 205 =
      (s.regs 205 |||
        ((if s.regs 180 < s.regs 200 then 1 else 0) |||
         (if s.regs 181 < s.regs 201 then 1 else 0))) ∧
      out.regs 205 ≤ 1 ∧
      out.regs 180 = s.regs 180 ∧
      out.regs 181 = s.regs 181 ∧ out.arr = s.arr := by
  have hb : s.regs 205 = 0 ∨ s.regs 205 = 1 := by omega
  rcases hb with hb | hb <;>
    (by_cases hL : s.regs 180 < s.regs 200) <;>
    (by_cases hU : s.regs 181 < s.regs 201) <;>
    simp_all [checkBody, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, denoteOp, rWrapL, rWrapU, rWrap, rBad,
      rOldL, rOldU, rLogL, rLogU, M]
  all_goals
    by_cases hL' : s.regs 180 < s.regs 200 <;>
      by_cases hU' : s.regs 181 < s.regs 201 <;>
      simp only [if_pos, if_neg, hL', hU'] <;> decide

/-- The existing arithmetic circuit computes both increments even when the
final endpoint additions wrap; this version deliberately retains the two
`mod 2^64` results. -/
theorem candidateBody_run_mod (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40)
    (hGate : s.regs 11 ≤ 1) :
    let out := arun k s candidateBody
    out.regs rLogL =
        (s.regs rLogL + s.regs 11 * incLWord (s.regs 132)) % M ∧
      out.regs rLogU =
        (s.regs rLogU + s.regs 11 * incUWord (s.regs 132)) % M ∧
      out.regs rIL = incLWord (s.regs 132) ∧
      out.regs rIU = incUWord (s.regs 132) ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  let l := arun k s (lift lowerScalarBody)
  let u := arun k l (lift upperScalarBody)
  let out := arun k u (lift commitScalarBody)
  have hl := lowerScalarBody_run k s hn2 hn40
  change l.regs rIL = incLWord (s.regs 132) ∧
    l.regs 132 = s.regs 132 ∧ l.arr = s.arr at hl
  have hu := upperScalarBody_run k l (by rw [hl.2.1]; exact hn2)
    (by rw [hl.2.1]; exact hn40)
  change u.regs rIU = incUWord (l.regs 132) ∧
    u.regs 132 = l.regs 132 ∧ u.arr = l.arr at hu
  have huIL : u.regs rIL = incLWord (s.regs 132) := by
    rw [scalarBody_frame k rIL upperScalarBody (by decide) l, hl.1]
  have huIU : u.regs rIU = incUWord (s.regs 132) := by
    rw [hu.1, hl.2.1]
  have huGate : u.regs 11 = s.regs 11 := by
    rw [scalarBody_frame k 11 upperScalarBody (by decide) l,
      scalarBody_frame k 11 lowerScalarBody (by decide) s]
  have huLogL : u.regs rLogL = s.regs rLogL := by
    rw [scalarBody_frame k rLogL upperScalarBody (by decide) l,
      scalarBody_frame k rLogL lowerScalarBody (by decide) s]
  have huLogU : u.regs rLogU = s.regs rLogU := by
    rw [scalarBody_frame k rLogU upperScalarBody (by decide) l,
      scalarBody_frame k rLogU lowerScalarBody (by decide) s]
  have hLM : s.regs 11 * incLWord (s.regs 132) < M := by
    have hinc := LeanCompCert.Ports.RS62.incLWord_le (s.regs 132)
    have hfp : fpD < M := by decide
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hGate hinc) hfp
  have hUM : s.regs 11 * incUWord (s.regs 132) < M := by
    have hinc := LeanCompCert.Ports.RS62.incUWord_le (s.regs 132)
    have hsmall : fpD + s.regs 132 < M := by
      have : 2 ^ 48 + 2 ^ 40 < M := by decide
      have hle := Nat.add_le_add_left hn40 fpD
      exact Nat.lt_of_le_of_lt (by simpa [fpD] using hle) this
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hGate hinc)
      (by simpa using hsmall)
  have houtIL : out.regs rIL = u.regs rIL :=
    scalarBody_frame k rIL commitScalarBody (by decide) u
  have houtIU : out.regs rIU = u.regs rIU :=
    scalarBody_frame k rIU commitScalarBody (by decide) u
  have hc :
      out.regs rLogL = (u.regs rLogL + u.regs 11 * u.regs rIL) % M ∧
      out.regs rLogU = (u.regs rLogU + u.regs 11 * u.regs rIU) % M ∧
      out.regs 132 = u.regs 132 ∧ out.arr = u.arr := by
    let lm := arun k u (lift commitLowerMulBody)
    let la := arun k lm (lift commitLowerAddBody)
    let um := arun k la (lift commitUpperMulBody)
    let final := arun k um (lift commitUpperAddBody)
    have hlm := commitLowerMulBody_run k u (by rw [huGate, huIL]; exact hLM)
    change lm.regs rA = u.regs 11 * u.regs rIL at hlm
    have hlmLogL : lm.regs rLogL = u.regs rLogL :=
      scalarBody_frame k rLogL commitLowerMulBody (by decide) u
    have hla := commitLowerAddBody_run_mod k lm
    change la.regs rLogL = (lm.regs rLogL + lm.regs rA) % M at hla
    have hlaGate : la.regs 11 = u.regs 11 := by
      rw [scalarBody_frame k 11 commitLowerAddBody (by decide) lm,
        scalarBody_frame k 11 commitLowerMulBody (by decide) u]
    have hlaIU : la.regs rIU = u.regs rIU := by
      rw [scalarBody_frame k rIU commitLowerAddBody (by decide) lm,
        scalarBody_frame k rIU commitLowerMulBody (by decide) u]
    have hlaLogU : la.regs rLogU = u.regs rLogU := by
      rw [scalarBody_frame k rLogU commitLowerAddBody (by decide) lm,
        scalarBody_frame k rLogU commitLowerMulBody (by decide) u]
    have hum := commitUpperMulBody_run k la (by
      rw [hlaGate, hlaIU, huGate, huIU]
      exact hUM)
    change um.regs rB = la.regs 11 * la.regs rIU at hum
    have humLogL : um.regs rLogL = la.regs rLogL :=
      scalarBody_frame k rLogL commitUpperMulBody (by decide) la
    have humLogU : um.regs rLogU = la.regs rLogU :=
      scalarBody_frame k rLogU commitUpperMulBody (by decide) la
    have hua := commitUpperAddBody_run_mod k um
    change final.regs rLogU = (um.regs rLogU + um.regs rB) % M at hua
    have hfinalLogL : final.regs rLogL = um.regs rLogL :=
      scalarBody_frame k rLogL commitUpperAddBody (by decide) um
    have hfinal132 : final.regs 132 = u.regs 132 := by
      rw [scalarBody_frame k 132 commitUpperAddBody (by decide) um,
        scalarBody_frame k 132 commitUpperMulBody (by decide) la,
        scalarBody_frame k 132 commitLowerAddBody (by decide) lm,
        scalarBody_frame k 132 commitLowerMulBody (by decide) u]
    have hfinalArr : final.arr = u.arr := by
      simp only [final, um, la, lm, arun_lift_arr]
    have hfinal :
        final.regs rLogL = (u.regs rLogL + u.regs 11 * u.regs rIL) % M ∧
        final.regs rLogU = (u.regs rLogU + u.regs 11 * u.regs rIU) % M ∧
        final.regs 132 = u.regs 132 ∧ final.arr = u.arr := by
      rw [hfinalLogL, humLogL, hla, hlmLogL, hlm, hua, humLogU,
        hlaLogU, hum, hlaGate, hlaIU, hfinal132, hfinalArr]
      exact ⟨rfl, rfl, rfl, rfl⟩
    simpa only [out, commitScalarBody, lift_append, arun_append] using hfinal
  have result :
      out.regs rLogL =
          (s.regs rLogL + s.regs 11 * incLWord (s.regs 132)) % M ∧
        out.regs rLogU =
          (s.regs rLogU + s.regs 11 * incUWord (s.regs 132)) % M ∧
        out.regs rIL = incLWord (s.regs 132) ∧
        out.regs rIU = incUWord (s.regs 132) ∧
        out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
    rw [hc.1, huLogL, huGate, huIL, hc.2.1, huLogU, huGate, huIU,
      houtIL, huIL, houtIU, huIU, hc.2.2.1, hu.2.1, hl.2.1,
      hc.2.2.2, hu.2.2, hl.2.2]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  simpa only [candidateBody, arun_append] using result

/-! ## A zero checked step rules out both endpoint wraps -/

theorem or_eq_zero {a b : Nat} (h : a ||| b = 0) :
    a = 0 ∧ b = 0 := by
  have ha : a ≤ a ||| b := Nat.left_le_or
  have hb : b ≤ a ||| b := Nat.right_le_or
  omega

theorem no_wrap_of_not_lt_left {a d : Nat}
    (ha : a < M) (hd : d < M) (h : ¬ (a + d) % M < a) :
    a + d < M := by
  apply Nat.lt_of_not_ge
  intro hM
  have hsum : a + d < M + M := by omega
  apply h
  rw [Nat.mod_eq_sub_mod hM, Nat.mod_eq_of_lt (by omega)]
  omega

theorem candidateBody_frame (k r : Nat) (s : AState)
    (h : LeanCompCert.Verified.RegFrame.writes r
      (lowerScalarBody ++ upperScalarBody ++ commitScalarBody) = false) :
    (arun k s candidateBody).regs r = s.regs r := by
  have hf := scalarBody_frame k r
    (lowerScalarBody ++ upperScalarBody ++ commitScalarBody) h s
  simpa only [candidateBody, lift_append, arun_append] using hf

/-- One zero overflow verdict proves that the corresponding source additions
are ordinary natural additions.  The theorem is independent of the segment
length and performs no checkpoint computation in Lean. -/
theorem body_zero_sound (n0 k : Nat) (s : AState)
    (hkM : k < M) (hn2 : 2 ≤ (n0 - 1) + k)
    (hn40 : (n0 - 1) + k ≤ 2 ^ 40)
    (hnM : (n0 - 1) + k < M)
    (hGate : s.arr k ≤ 1)
    (hLogL : s.regs rLogL < M) (hLogU : s.regs rLogU < M)
    (hBad : s.regs rBad ≤ 1)
    (hZero : (arun k s (body n0)).regs rBad = 0) :
    s.regs rBad = 0 ∧
      s.regs rLogL + s.arr k * incLWord ((n0 - 1) + k) < M ∧
      s.regs rLogU + s.arr k * incUWord ((n0 - 1) + k) < M ∧
      (arun k s (body n0)).regs rLogL =
        s.regs rLogL + s.arr k * incLWord ((n0 - 1) + k) ∧
      (arun k s (body n0)).regs rLogU =
        s.regs rLogU + s.arr k * incUWord ((n0 - 1) + k) ∧
      (arun k s (body n0)).arr = s.arr := by
  let saved := arun k s saveBody
  let pre := arun k saved (RS62PrimeMaskLadder.maskPrefix n0)
  let cand := arun k pre candidateBody
  let out := arun k cand checkBody
  have hs := saveBody_run k s
  change saved.regs rOldL = s.regs rLogL ∧
    saved.regs rOldU = s.regs rLogU ∧
    saved.regs rLogL = s.regs rLogL ∧
    saved.regs rLogU = s.regs rLogU ∧
    saved.regs rBad = s.regs rBad ∧ saved.arr = s.arr at hs
  rcases hs with ⟨hsOldL, hsOldU, hsL, hsU, hsBad, hsArr⟩
  have hp := RS62PrimeMaskLadder.maskPrefix_run n0 k saved hkM hnM
  change pre.regs RS62PrimeMaskLadder.rAddr = k ∧
    pre.regs RS62PrimeMaskLadder.rGate = saved.arr k ∧
    pre.regs RS62PrimeMaskLadder.rN = (n0 - 1) + k ∧
    pre.regs rLogL = saved.regs rLogL ∧
    pre.regs rLogU = saved.regs rLogU ∧ pre.arr = saved.arr at hp
  rcases hp with ⟨hpAddr, hpGate, hpN, hpL, hpU, hpArr⟩
  have hpFrame : pre.regs rOldL = saved.regs rOldL ∧
      pre.regs rOldU = saved.regs rOldU ∧
      pre.regs rBad = saved.regs rBad := by
    simp [pre, RS62PrimeMaskLadder.maskPrefix, arun, astep,
      AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      rOldL, rOldU, rBad, RS62PrimeMaskLadder.rAddr,
      RS62PrimeMaskLadder.rGate, RS62PrimeMaskLadder.rN]
  rcases hpFrame with ⟨hpOldL, hpOldU, hpBad⟩
  have hc := candidateBody_run_mod k pre
    (by rw [hpN]; exact hn2)
    (by rw [hpN]; exact hn40)
    (by rw [hpGate, hsArr]; exact hGate)
  change cand.regs rLogL =
      (pre.regs rLogL + pre.regs RS62PrimeMaskLadder.rGate *
        incLWord (pre.regs RS62PrimeMaskLadder.rN)) % M ∧
    cand.regs rLogU =
      (pre.regs rLogU + pre.regs RS62PrimeMaskLadder.rGate *
        incUWord (pre.regs RS62PrimeMaskLadder.rN)) % M ∧
    cand.regs rIL = incLWord (pre.regs RS62PrimeMaskLadder.rN) ∧
    cand.regs rIU = incUWord (pre.regs RS62PrimeMaskLadder.rN) ∧
    cand.regs RS62PrimeMaskLadder.rN = pre.regs RS62PrimeMaskLadder.rN ∧
    cand.arr = pre.arr at hc
  rcases hc with ⟨hcLmod, hcUmod, hcIL, hcIU, hcN, hcArr⟩
  have hcOldL : cand.regs rOldL = pre.regs rOldL :=
    candidateBody_frame k rOldL pre (by decide)
  have hcOldU : cand.regs rOldU = pre.regs rOldU :=
    candidateBody_frame k rOldU pre (by decide)
  have hcBad : cand.regs rBad = pre.regs rBad :=
    candidateBody_frame k rBad pre (by decide)
  have hcBadLe : cand.regs rBad ≤ 1 := by
    rw [hcBad, hpBad, hsBad]
    exact hBad
  have hcheck := checkBody_run k cand hcBadLe
  change out.regs rBad =
      (cand.regs rBad |||
        ((if cand.regs rLogL < cand.regs rOldL then 1 else 0) |||
         (if cand.regs rLogU < cand.regs rOldU then 1 else 0))) ∧
    out.regs rBad ≤ 1 ∧ out.regs rLogL = cand.regs rLogL ∧
    out.regs rLogU = cand.regs rLogU ∧ out.arr = cand.arr at hcheck
  have houtEq : arun k s (body n0) = out := by
    simp only [body, RS62PrimeMaskLadder.body, arun_append, saved, pre, cand,
      out]
  have houtZero : out.regs rBad = 0 := by rw [← houtEq]; exact hZero
  have hz := or_eq_zero (hcheck.1.symm.trans houtZero)
  have hflags := or_eq_zero hz.2
  have hnL : ¬ cand.regs rLogL < cand.regs rOldL := by
    intro h
    simp [h] at hflags
  have hnU : ¬ cand.regs rLogU < cand.regs rOldU := by
    intro h
    simp [h] at hflags
  let dL := s.arr k * incLWord ((n0 - 1) + k)
  let dU := s.arr k * incUWord ((n0 - 1) + k)
  have hdL : dL < M := by
    have hi := LeanCompCert.Ports.RS62.incLWord_le ((n0 - 1) + k)
    have hfp : fpD < M := by decide
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hGate hi) hfp
  have hdU : dU < M := by
    have hi := LeanCompCert.Ports.RS62.incUWord_le ((n0 - 1) + k)
    have hsmall : fpD + ((n0 - 1) + k) < M := by
      have : 2 ^ 48 + 2 ^ 40 < M := by decide
      exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hn40 fpD) this
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hGate hi) (by simpa using hsmall)
  have hcL : cand.regs rLogL = (s.regs rLogL + dL) % M := by
    rw [hcLmod, hpL, hsL, hpGate, hpN]
    rfl
  have hcU : cand.regs rLogU = (s.regs rLogU + dU) % M := by
    rw [hcUmod, hpU, hsU, hpGate, hpN]
    rfl
  have holdL : cand.regs rOldL = s.regs rLogL := by
    rw [hcOldL, hpOldL, hsOldL]
  have holdU : cand.regs rOldU = s.regs rLogU := by
    rw [hcOldU, hpOldU, hsOldU]
  have hsumL : s.regs rLogL + dL < M :=
    no_wrap_of_not_lt_left hLogL hdL (by rw [← hcL, ← holdL]; exact hnL)
  have hsumU : s.regs rLogU + dU < M :=
    no_wrap_of_not_lt_left hLogU hdU (by rw [← hcU, ← holdU]; exact hnU)
  refine ⟨?_, by simpa only [dL] using hsumL,
    by simpa only [dU] using hsumU, ?_, ?_, ?_⟩
  · rw [← hsBad, ← hpBad, ← hcBad]
    exact hz.1
  · rw [houtEq, hcheck.2.2.1, hcL, Nat.mod_eq_of_lt hsumL]
  · rw [houtEq, hcheck.2.2.2.1, hcU, Nat.mod_eq_of_lt hsumU]
  · rw [houtEq, hcheck.2.2.2.2, hcArr, hpArr, hsArr]

/-! ## Symbolic lifting over an arbitrary compiled segment -/

/-- The failure latch remains a bit and is monotone.  This is deliberately
separate from arithmetic soundness: it lets a final zero verdict be pushed
back to every prefix without evaluating any prefix in Lean. -/
theorem body_bad_monotone (n0 k : Nat) (s : AState)
    (hBad : s.regs rBad ≤ 1) :
    (arun k s (body n0)).regs rBad ≤ 1 ∧
      s.regs rBad ≤ (arun k s (body n0)).regs rBad := by
  let saved := arun k s saveBody
  let pre := arun k saved (RS62PrimeMaskLadder.maskPrefix n0)
  let cand := arun k pre candidateBody
  let out := arun k cand checkBody
  have hs := saveBody_run k s
  change saved.regs rOldL = s.regs rLogL ∧
    saved.regs rOldU = s.regs rLogU ∧
    saved.regs rLogL = s.regs rLogL ∧
    saved.regs rLogU = s.regs rLogU ∧
    saved.regs rBad = s.regs rBad ∧ saved.arr = s.arr at hs
  have hpBad : pre.regs rBad = saved.regs rBad := by
    simp [pre, RS62PrimeMaskLadder.maskPrefix, arun, astep,
      AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      rBad, RS62PrimeMaskLadder.rAddr, RS62PrimeMaskLadder.rGate,
      RS62PrimeMaskLadder.rN]
  have hcBad : cand.regs rBad = pre.regs rBad :=
    candidateBody_frame k rBad pre (by decide)
  have hcBadLe : cand.regs rBad ≤ 1 := by
    rw [hcBad, hpBad, hs.2.2.2.2.1]
    exact hBad
  have hcheck := checkBody_run k cand hcBadLe
  change out.regs rBad =
      (cand.regs rBad |||
        ((if cand.regs rLogL < cand.regs rOldL then 1 else 0) |||
         (if cand.regs rLogU < cand.regs rOldU then 1 else 0))) ∧
    out.regs rBad ≤ 1 ∧ out.regs rLogL = cand.regs rLogL ∧
    out.regs rLogU = cand.regs rLogU ∧ out.arr = cand.arr at hcheck
  have houtEq : arun k s (body n0) = out := by
    simp only [body, RS62PrimeMaskLadder.body, arun_append, saved, pre, cand,
      out]
  rw [houtEq]
  refine ⟨hcheck.2.1, ?_⟩
  calc
    s.regs rBad = cand.regs rBad := by
      rw [hcBad, hpBad, hs.2.2.2.2.1]
    _ ≤ cand.regs rBad |||
        ((if cand.regs rLogL < cand.regs rOldL then 1 else 0) |||
         (if cand.regs rLogU < cand.regs rOldU then 1 else 0)) :=
      Nat.left_le_or
    _ = out.regs rBad := hcheck.1.symm

theorem body_arr (n0 k : Nat) (s : AState) :
    (arun k s (body n0)).arr = s.arr := by
  simp [body, saveBody, checkBody, RS62PrimeMaskLadder.body,
    RS62PrimeMaskLadder.maskPrefix, candidateBody, arun_append,
    arun_lift_arr, arun, astep, AState.writeReg]

/-- Total checked machine fold used by the physical run receipt. -/
def machineFoldState (arr : Nat → Nat) (n0 f SL SU : Nat) : AState :=
  (List.range f).foldl (fun s k => arun k s (body n0))
    (arun 0 (initialAStateWithArray arr)
      (RS62PrimeMaskLadder.init SL SU ++
        [AInstr.scalar (.mov rBad (.lit 0))]))

theorem machineFoldState_succ (arr : Nat → Nat)
    (n0 f SL SU : Nat) :
    machineFoldState arr n0 (f + 1) SL SU =
      arun f (machineFoldState arr n0 f SL SU) (body n0) := by
  unfold machineFoldState
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem machineFoldState_arr (arr : Nat → Nat)
    (n0 f SL SU : Nat) :
    (machineFoldState arr n0 f SL SU).arr = arr := by
  induction f with
  | zero =>
      simp [machineFoldState, RS62PrimeMaskLadder.init, arun, astep,
        initialAStateWithArray, AState.writeReg]
  | succ f ih =>
      rw [machineFoldState_succ, body_arr, ih]

theorem machineFoldState_bad_le (arr : Nat → Nat)
    (n0 f SL SU : Nat) :
    (machineFoldState arr n0 f SL SU).regs rBad ≤ 1 := by
  induction f with
  | zero =>
      simp [machineFoldState, RS62PrimeMaskLadder.init, arun, astep,
        initialAStateWithArray, AState.writeReg, sdest, sval, denoteOperand,
        rBad]
  | succ f ih =>
      rw [machineFoldState_succ]
      exact (body_bad_monotone n0 f
        (machineFoldState arr n0 f SL SU) ih).1

/-- A zero final latch proves all source prefix additions are non-wrapping
and that the checked machine has exactly the pure mask-fold endpoints. -/
theorem machineFoldState_zero_sound (arr : Nat → Nat)
    (n0 f SL SU : Nat) (hn0 : 3 ≤ n0)
    (hSL : SL < M) (hSU : SU < M) (hfM : f < M)
    (hEnd : n0 + f ≤ 2 ^ 40)
    (hMaskBit : ∀ k, k < f → arr k ≤ 1)
    (hZero : (machineFoldState arr n0 f SL SU).regs rBad = 0) :
    RS62PrimeMaskLadder.Room arr n0 f SL SU ∧
      (machineFoldState arr n0 f SL SU).regs rLogL =
        (RS62PrimeMaskLadder.maskFold arr n0 f SL SU).1 ∧
      (machineFoldState arr n0 f SL SU).regs rLogU =
        (RS62PrimeMaskLadder.maskFold arr n0 f SL SU).2 ∧
      (machineFoldState arr n0 f SL SU).arr = arr ∧
      (machineFoldState arr n0 f SL SU).regs rLogL < M ∧
      (machineFoldState arr n0 f SL SU).regs rLogU < M := by
  induction f with
  | zero =>
      constructor
      · intro k hk
        omega
      · simpa [machineFoldState, RS62PrimeMaskLadder.maskFold,
          RS62PrimeMaskLadder.init, arun, astep, initialAStateWithArray,
          AState.writeReg, sdest, sval, denoteOperand,
          Nat.mod_eq_of_lt hSL, Nat.mod_eq_of_lt hSU, rBad, rLogL, rLogU,
          LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL,
          LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU] using
          (show SL < M ∧ SU < M from ⟨hSL, hSU⟩)
  | succ f ih =>
      let mid := machineFoldState arr n0 f SL SU
      let out := machineFoldState arr n0 (f + 1) SL SU
      have hfM' : f < M := by omega
      have hEnd' : n0 + f ≤ 2 ^ 40 := by omega
      have hMaskBit' : ∀ k, k < f → arr k ≤ 1 := by
        intro k hk
        exact hMaskBit k (by omega)
      have hmidBadLe := machineFoldState_bad_le arr n0 f SL SU
      have hmono := body_bad_monotone n0 f mid hmidBadLe
      have houtEq : out = arun f mid (body n0) := by
        simp only [out, mid, machineFoldState_succ]
      have houtZero : out.regs rBad = 0 := by exact hZero
      have hmidZero : mid.regs rBad = 0 := by
        have : mid.regs rBad ≤ out.regs rBad := by
          rw [houtEq]
          exact hmono.2
        omega
      have hmid := ih hfM' hEnd' hMaskBit' hmidZero
      rcases hmid with ⟨hroomMid, hmidL, hmidU, hmidArr, hmidLM, hmidUM⟩
      change mid.regs rLogL =
        (RS62PrimeMaskLadder.maskFold arr n0 f SL SU).1 at hmidL
      change mid.regs rLogU =
        (RS62PrimeMaskLadder.maskFold arr n0 f SL SU).2 at hmidU
      change mid.arr = arr at hmidArr
      change mid.regs rLogL < M at hmidLM
      change mid.regs rLogU < M at hmidUM
      have h40M : 2 ^ 40 < M := by decide
      have hstep := body_zero_sound n0 f mid
        (by omega) (by omega) (by omega) (by omega)
        (by rw [hmidArr]; exact hMaskBit f (by omega))
        hmidLM hmidUM hmidBadLe
        (by rw [← houtEq]; exact houtZero)
      rcases hstep with
        ⟨hstepBad, hsumL, hsumU, hstepL, hstepU, hstepArr⟩
      have hroom : RS62PrimeMaskLadder.Room arr n0 (f + 1) SL SU := by
        intro k hk
        by_cases hkf : k < f
        · exact hroomMid k hkf
        · have hkEq : k = f := by omega
          subst hkEq
          dsimp only
          exact ⟨by simpa only [hmidL, hmidArr] using hsumL,
            by simpa only [hmidU, hmidArr] using hsumU⟩
      rw [RS62PrimeMaskLadder.maskFold_succ]
      change RS62PrimeMaskLadder.Room arr n0 (f + 1) SL SU ∧
        out.regs rLogL =
          (RS62PrimeMaskLadder.maskStep arr n0
            (RS62PrimeMaskLadder.maskFold arr n0 f SL SU) f).1 ∧
        out.regs rLogU =
          (RS62PrimeMaskLadder.maskStep arr n0
            (RS62PrimeMaskLadder.maskFold arr n0 f SL SU) f).2 ∧
        out.arr = arr ∧ out.regs rLogL < M ∧ out.regs rLogU < M
      dsimp only [RS62PrimeMaskLadder.maskStep]
      refine ⟨hroom, ?_, ?_, ?_, ?_, ?_⟩
      · rw [houtEq, hstepL, hmidL, hmidArr]
      · rw [houtEq, hstepU, hmidU, hmidArr]
      · rw [houtEq, hstepArr, hmidArr]
      · rw [houtEq, hstepL]
        exact hsumL
      · rw [houtEq, hstepU]
        exact hsumU

/-- Receipt-facing bridge: a zero CompCert-run verdict supplies `Room` and
the exact RS62 source recurrence.  The only finite data premise is the
caller-owned mask contract; no production fold is reduced by the kernel. -/
theorem source_loopE_of_runFromArray_zero (p : Nat → Bool)
    (arr : Nat → Nat) (n0 f SL SU : Nat)
    (hn0 : 3 ≤ n0) (hSL : SL < M) (hSU : SU < M)
    (hfM : f < M) (hEnd : n0 + f ≤ 2 ^ 40)
    (hmask : RS62PrimeMaskLadder.MaskCorrect p arr n0 f)
    (out : AState)
    (hRun : (program n0 f SL SU rBad).runFromArray arr = some out)
    (hZero : out.regs rBad = 0) :
    RS62PrimeMaskLadder.Room arr n0 f SL SU ∧
      out.regs rLogL = (LeanCompCert.Ports.RS62.loopE p f n0 SL SU).1 ∧
      out.regs rLogU = (LeanCompCert.Ports.RS62.loopE p f n0 SL SU).2 ∧
      out.arr = arr := by
  have hout := AProgram.eq_arun_of_runFromArray_eq_some
    (program n0 f SL SU rBad) arr out hRun
  have houtEq : out = machineFoldState arr n0 f SL SU := by
    simpa [program, machineFoldState, arun] using hout
  have hMaskBit : ∀ k, k < f → arr k ≤ 1 := by
    intro k hk
    rw [hmask k hk]
    split <;> omega
  have hsound := machineFoldState_zero_sound arr n0 f SL SU
    hn0 hSL hSU hfM hEnd hMaskBit (by rw [← houtEq]; exact hZero)
  rw [← RS62PrimeMaskLadder.maskFold_eq_loopE p arr n0 f SL SU hn0 hmask]
  exact ⟨hsound.1, by rw [houtEq]; exact hsound.2.1,
    by rw [houtEq]; exact hsound.2.2.1,
    by rw [houtEq]; exact hsound.2.2.2.1⟩

#print axioms program_wf
#print axioms body_zero_sound
#print axioms machineFoldState_zero_sound
#print axioms source_loopE_of_runFromArray_zero

end LeanCompCert.Ports.RS62PrimeMaskLadderOverflow
