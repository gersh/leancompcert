import LeanCompCert.Ports.R2RuntimeFailureObservation
import LeanCompCert.Ports.R2SegLogLinear
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# Local counter semantics for the compiled R2 inequality clauses

The two paper-bound comparisons each have a dedicated monotone failure
counter.  This file starts their telescope by isolating the literal
instruction islands and proving the exact increment of `rVUp` and `rVLo`.
The production fold can therefore turn a retained terminal zero into a
per-event comparison without replaying any numerical event in Lean.
-/

namespace LeanCompCert.Ports.R2SegSieve

set_option maxRecDepth 10000

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.InstrBlock

/-- Literal instructions 293--297 and the two failure-counter commits. -/
def logClauseOneInstrs (S : Nat) : List Instr :=
  [ .binop 293 .add (.reg rD) (.reg rErr)
  , .binop 294 .add (.reg 293) (.reg rNe)
  , .binop 295 .add (.lit (biasOf S)) (.reg rThr)
  , .binop 296 .gt (.reg 294) (.reg 295)
  , .binop 297 .mul (.reg 296) (.reg 247)
  , .binop rViol .add (.reg rViol) (.reg 297)
  , .binop rVUp .add (.reg rVUp) (.reg 297) ]

def logClauseOneLiteralBody (S : Nat) : List AInstr :=
  lift (logClauseOneInstrs S)

theorem logClauseOneLiteralBody_eq_slice (c : R2Cfg) :
    logClauseOneBody c = logClauseOneLiteralBody c.sc := by
  rfl

def clauseOneFailure (S d err n thr fin : Nat) : Nat :=
  (if biasOf S + thr < d + err + n then 1 else 0) * fin

theorem clauseOneFailure_le_fin (S d err n thr fin : Nat) :
    clauseOneFailure S d err n thr fin ≤ fin := by
  simp only [clauseOneFailure]
  split <;> omega

/-- The upper-clause island adds exactly its gated comparison bit. -/
theorem logClauseOneInstrs_vup_run
    (k : Nat) (s : RegState) (S d err n thr fin up : Nat)
    (hd : s rD = d) (herr : s rErr = err) (hn : s rNe = n)
    (hthr : s rThr = thr) (hfin : s 247 = fin) (hup : s rVUp = up)
    (hde : d + err < M) (hden : d + err + n < M)
    (hbt : biasOf S + thr < M)
    (hroom : up + clauseOneFailure S d err n thr fin < M) :
    (srun k s (logClauseOneInstrs S)) rVUp =
      up + clauseOneFailure S d err n thr fin := by
  have hd' : s 180 = d := by simpa only [rD] using hd
  have herr' : s 181 = err := by simpa only [rErr] using herr
  have hn' : s 194 = n := by simpa only [rNe] using hn
  have hthr' : s 189 = thr := by simpa only [rThr] using hthr
  have hup' : s 350 = up := by simpa only [rVUp] using hup
  by_cases hcmp : biasOf S + thr < d + err + n
  · have hroom' : up + fin < M := by
      simpa only [clauseOneFailure, if_pos hcmp, Nat.one_mul] using hroom
    simp [logClauseOneInstrs, clauseOneFailure, srun, RegState.set,
      sdest, sval, denoteOperand, denoteOp, hd', herr', hn', hthr', hfin,
      hup', hcmp, rD, rErr, rNe, rThr, rViol, rVUp,
      Nat.mod_eq_of_lt hde, Nat.mod_eq_of_lt hden,
      Nat.mod_eq_of_lt hbt, Nat.mod_eq_of_lt hroom']
  · have hupM : up < M := by
      simpa only [clauseOneFailure, if_neg hcmp, Nat.zero_mul, Nat.add_zero]
        using hroom
    simp [logClauseOneInstrs, clauseOneFailure, srun, RegState.set,
      sdest, sval, denoteOperand, denoteOp, hd', herr', hn', hthr', hfin,
      hup', hcmp, rD, rErr, rNe, rThr, rViol, rVUp,
      Nat.mod_eq_of_lt hde, Nat.mod_eq_of_lt hden,
      Nat.mod_eq_of_lt hbt, Nat.mod_eq_of_lt hupM]

/-- On a nonfinal logarithm round the comparison result is annihilated by the
literal finish gate, so none of the comparison-side additions need a
no-wrap hypothesis. -/
theorem logClauseOneInstrs_vup_run_zero
    (k : Nat) (s : RegState) (S up : Nat)
    (hfin : s 247 = 0) (hup : s rVUp = up) (hupM : up < M) :
    (srun k s (logClauseOneInstrs S)) rVUp = up := by
  have hup' : s 350 = up := by simpa only [rVUp] using hup
  simp [logClauseOneInstrs, srun, RegState.set, sdest, sval, denoteOperand,
    denoteOp, hfin, hup', rViol, rVUp, Nat.mod_eq_of_lt hupM]

theorem logClauseOneBody_vup_run
    (c : R2Cfg) (k : Nat) (s : AState) (d err n thr fin up : Nat)
    (hd : s.regs rD = d) (herr : s.regs rErr = err)
    (hn : s.regs rNe = n) (hthr : s.regs rThr = thr)
    (hfin : s.regs 247 = fin) (hup : s.regs rVUp = up)
    (hde : d + err < M) (hden : d + err + n < M)
    (hbt : biasOf c.sc + thr < M)
    (hroom : up + clauseOneFailure c.sc d err n thr fin < M) :
    (arun k s (logClauseOneBody c)).regs rVUp =
      up + clauseOneFailure c.sc d err n thr fin := by
  rw [logClauseOneLiteralBody_eq_slice, logClauseOneLiteralBody,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact logClauseOneInstrs_vup_run k s.regs c.sc d err n thr fin up
    hd herr hn hthr hfin hup hde hden hbt hroom

theorem logClauseOneBody_vup_run_zero
    (c : R2Cfg) (k : Nat) (s : AState) (up : Nat)
    (hfin : s.regs 247 = 0) (hup : s.regs rVUp = up) (hupM : up < M) :
    (arun k s (logClauseOneBody c)).regs rVUp = up := by
  rw [logClauseOneLiteralBody_eq_slice, logClauseOneLiteralBody,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact logClauseOneInstrs_vup_run_zero k s.regs c.sc up hfin hup hupM

/-! ## The post-jump lower clause -/

/-- Literal instructions 321--324 and the two failure-counter commits. -/
def logClauseTwoInstrs (S : Nat) : List Instr :=
  [ .binop 321 .add (.reg rD) (.reg rThr)
  , .binop 322 .add (.lit (biasOf S)) (.reg rErr)
  , .binop 323 .lt (.reg 321) (.reg 322)
  , .binop 324 .mul (.reg 323) (.reg 247)
  , .binop rViol .add (.reg rViol) (.reg 324)
  , .binop rVLo .add (.reg rVLo) (.reg 324) ]

def logClauseTwoBody (S : Nat) : List AInstr :=
  lift (logClauseTwoInstrs S)

theorem logClauseTwoBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 148).take 6 = logClauseTwoBody c.sc := by
  rfl

def clauseTwoFailure (S d err thr fin : Nat) : Nat :=
  (if d + thr < biasOf S + err then 1 else 0) * fin

theorem clauseTwoFailure_le_fin (S d err thr fin : Nat) :
    clauseTwoFailure S d err thr fin ≤ fin := by
  simp only [clauseTwoFailure]
  split <;> omega

/-- The lower-clause island adds exactly its gated comparison bit. -/
theorem logClauseTwoInstrs_vlo_run
    (k : Nat) (s : RegState) (S d err thr fin lo : Nat)
    (hd : s rD = d) (herr : s rErr = err) (hthr : s rThr = thr)
    (hfin : s 247 = fin) (hlo : s rVLo = lo)
    (hdt : d + thr < M) (hbe : biasOf S + err < M)
    (hroom : lo + clauseTwoFailure S d err thr fin < M) :
    (srun k s (logClauseTwoInstrs S)) rVLo =
      lo + clauseTwoFailure S d err thr fin := by
  have hd' : s 180 = d := by simpa only [rD] using hd
  have herr' : s 181 = err := by simpa only [rErr] using herr
  have hthr' : s 189 = thr := by simpa only [rThr] using hthr
  have hlo' : s 351 = lo := by simpa only [rVLo] using hlo
  by_cases hcmp : d + thr < biasOf S + err
  · have hroom' : lo + fin < M := by
      simpa only [clauseTwoFailure, if_pos hcmp, Nat.one_mul] using hroom
    simp [logClauseTwoInstrs, clauseTwoFailure, srun, RegState.set,
      sdest, sval, denoteOperand, denoteOp, hd', herr', hthr', hfin, hlo',
      hcmp, rD, rErr, rThr, rViol, rVLo,
      Nat.mod_eq_of_lt hdt, Nat.mod_eq_of_lt hbe,
      Nat.mod_eq_of_lt hroom']
  · have hloM : lo < M := by
      simpa only [clauseTwoFailure, if_neg hcmp, Nat.zero_mul, Nat.add_zero]
        using hroom
    simp [logClauseTwoInstrs, clauseTwoFailure, srun, RegState.set,
      sdest, sval, denoteOperand, denoteOp, hd', herr', hthr', hfin, hlo',
      hcmp, rD, rErr, rThr, rViol, rVLo,
      Nat.mod_eq_of_lt hdt, Nat.mod_eq_of_lt hbe,
      Nat.mod_eq_of_lt hloM]

/-- Nonfinal lower-clause rounds likewise leave their counter unchanged
without requiring either comparison addition to be unwrapped. -/
theorem logClauseTwoInstrs_vlo_run_zero
    (k : Nat) (s : RegState) (S lo : Nat)
    (hfin : s 247 = 0) (hlo : s rVLo = lo) (hloM : lo < M) :
    (srun k s (logClauseTwoInstrs S)) rVLo = lo := by
  have hlo' : s 351 = lo := by simpa only [rVLo] using hlo
  simp [logClauseTwoInstrs, srun, RegState.set, sdest, sval, denoteOperand,
    denoteOp, hfin, hlo', rViol, rVLo, Nat.mod_eq_of_lt hloM]

theorem logClauseTwoBody_vlo_run
    (c : R2Cfg) (k : Nat) (s : AState) (d err thr fin lo : Nat)
    (hd : s.regs rD = d) (herr : s.regs rErr = err)
    (hthr : s.regs rThr = thr) (hfin : s.regs 247 = fin)
    (hlo : s.regs rVLo = lo)
    (hdt : d + thr < M) (hbe : biasOf c.sc + err < M)
    (hroom : lo + clauseTwoFailure c.sc d err thr fin < M) :
    (arun k s (logClauseTwoBody c.sc)).regs rVLo =
      lo + clauseTwoFailure c.sc d err thr fin := by
  rw [logClauseTwoBody,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact logClauseTwoInstrs_vlo_run k s.regs c.sc d err thr fin lo
    hd herr hthr hfin hlo hdt hbe hroom

theorem logClauseTwoBody_vlo_run_zero
    (S : Nat) (k : Nat) (s : AState) (lo : Nat)
    (hfin : s.regs 247 = 0) (hlo : s.regs rVLo = lo) (hloM : lo < M) :
    (arun k s (logClauseTwoBody S)).regs rVLo = lo := by
  rw [logClauseTwoBody,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact logClauseTwoInstrs_vlo_run_zero k s.regs S lo hfin hlo hloM

/-! ## Exact increments in one complete scheduled body -/

def bodyBeforeClauseOne (c : R2Cfg) : List AInstr :=
  c.markBody ++ c.classBody ++ c.logBody.take 107

def bodyAfterClauseOne (c : R2Cfg) : List AInstr :=
  c.logBody.drop 114 ++ c.tailBody

theorem body_eq_clauseOne_stages (c : R2Cfg) :
    c.body = bodyBeforeClauseOne c ++ logClauseOneBody c ++
      bodyAfterClauseOne c := by
  rfl

def beforeClauseOne (c : R2Cfg) (k : Nat) (s : AState) : AState :=
  arun k s (bodyBeforeClauseOne c)

/-- One scheduled body adds exactly the upper-clause bit observed at the
literal comparison boundary. -/
theorem body_vup_increment (c : R2Cfg) (k : Nat) (s : AState)
    (hde :
      let pre := beforeClauseOne c k s
      pre.regs rD + pre.regs rErr < M)
    (hden :
      let pre := beforeClauseOne c k s
      pre.regs rD + pre.regs rErr + pre.regs rNe < M)
    (hbt :
      let pre := beforeClauseOne c k s
      biasOf c.sc + pre.regs rThr < M)
    (hroom :
      let pre := beforeClauseOne c k s
      s.regs rVUp + clauseOneFailure c.sc (pre.regs rD)
        (pre.regs rErr) (pre.regs rNe) (pre.regs rThr)
        (pre.regs 247) < M) :
    let pre := beforeClauseOne c k s
    (arun k s c.body).regs rVUp =
      s.regs rVUp + clauseOneFailure c.sc (pre.regs rD)
        (pre.regs rErr) (pre.regs rNe) (pre.regs rThr)
        (pre.regs 247) := by
  let pre := beforeClauseOne c k s
  let guarded := arun k pre (logClauseOneBody c)
  have hpreFrame : pre.regs rVUp = s.regs rVUp :=
    arun_frame k rVUp (bodyBeforeClauseOne c) (by rfl) s
  have hguard := logClauseOneBody_vup_run c k pre
    (pre.regs rD) (pre.regs rErr) (pre.regs rNe) (pre.regs rThr)
    (pre.regs 247) (s.regs rVUp) rfl rfl rfl rfl rfl hpreFrame
    hde hden hbt hroom
  have hsuffix :
      (arun k guarded (bodyAfterClauseOne c)).regs rVUp =
        guarded.regs rVUp :=
    arun_frame k rVUp (bodyAfterClauseOne c) (by rfl) guarded
  rw [body_eq_clauseOne_stages, arun_append, arun_append]
  exact hsuffix.trans hguard

theorem body_vup_increment_nonfinal (c : R2Cfg) (k : Nat) (s : AState)
    (hfin :
      let pre := beforeClauseOne c k s
      pre.regs 247 = 0)
    (hupM : s.regs rVUp < M) :
    (arun k s c.body).regs rVUp = s.regs rVUp := by
  let pre := beforeClauseOne c k s
  let guarded := arun k pre (logClauseOneBody c)
  have hpreFrame : pre.regs rVUp = s.regs rVUp :=
    arun_frame k rVUp (bodyBeforeClauseOne c) (by rfl) s
  have hguard := logClauseOneBody_vup_run_zero c k pre (s.regs rVUp)
    hfin hpreFrame hupM
  have hsuffix :
      (arun k guarded (bodyAfterClauseOne c)).regs rVUp =
        guarded.regs rVUp :=
    arun_frame k rVUp (bodyAfterClauseOne c) (by rfl) guarded
  rw [body_eq_clauseOne_stages, arun_append, arun_append]
  exact hsuffix.trans hguard

def bodyBeforeClauseTwo (c : R2Cfg) : List AInstr :=
  c.markBody ++ c.classBody ++ c.logBody.take 148

def bodyAfterClauseTwo (c : R2Cfg) : List AInstr :=
  c.logBody.drop 154 ++ c.tailBody

theorem body_eq_clauseTwo_stages (c : R2Cfg) :
    c.body = bodyBeforeClauseTwo c ++ logClauseTwoBody c.sc ++
      bodyAfterClauseTwo c := by
  rfl

def beforeClauseTwo (c : R2Cfg) (k : Nat) (s : AState) : AState :=
  arun k s (bodyBeforeClauseTwo c)

/-- One scheduled body adds exactly the lower-clause bit observed at the
literal comparison boundary. -/
theorem body_vlo_increment (c : R2Cfg) (k : Nat) (s : AState)
    (hdt :
      let pre := beforeClauseTwo c k s
      pre.regs rD + pre.regs rThr < M)
    (hbe :
      let pre := beforeClauseTwo c k s
      biasOf c.sc + pre.regs rErr < M)
    (hroom :
      let pre := beforeClauseTwo c k s
      s.regs rVLo + clauseTwoFailure c.sc (pre.regs rD)
        (pre.regs rErr) (pre.regs rThr) (pre.regs 247) < M) :
    let pre := beforeClauseTwo c k s
    (arun k s c.body).regs rVLo =
      s.regs rVLo + clauseTwoFailure c.sc (pre.regs rD)
        (pre.regs rErr) (pre.regs rThr) (pre.regs 247) := by
  let pre := beforeClauseTwo c k s
  let guarded := arun k pre (logClauseTwoBody c.sc)
  have hpreFrame : pre.regs rVLo = s.regs rVLo :=
    arun_frame k rVLo (bodyBeforeClauseTwo c) (by rfl) s
  have hguard := logClauseTwoBody_vlo_run c k pre
    (pre.regs rD) (pre.regs rErr) (pre.regs rThr) (pre.regs 247)
    (s.regs rVLo) rfl rfl rfl rfl hpreFrame hdt hbe hroom
  have hsuffix :
      (arun k guarded (bodyAfterClauseTwo c)).regs rVLo =
        guarded.regs rVLo :=
    arun_frame k rVLo (bodyAfterClauseTwo c) (by rfl) guarded
  rw [body_eq_clauseTwo_stages, arun_append, arun_append]
  exact hsuffix.trans hguard

theorem body_vlo_increment_nonfinal (c : R2Cfg) (k : Nat) (s : AState)
    (hfin :
      let pre := beforeClauseTwo c k s
      pre.regs 247 = 0)
    (hloM : s.regs rVLo < M) :
    (arun k s c.body).regs rVLo = s.regs rVLo := by
  let pre := beforeClauseTwo c k s
  let guarded := arun k pre (logClauseTwoBody c.sc)
  have hpreFrame : pre.regs rVLo = s.regs rVLo :=
    arun_frame k rVLo (bodyBeforeClauseTwo c) (by rfl) s
  have hguard := logClauseTwoBody_vlo_run_zero c.sc k pre (s.regs rVLo)
    hfin hpreFrame hloM
  have hsuffix :
      (arun k guarded (bodyAfterClauseTwo c)).regs rVLo =
        guarded.regs rVLo :=
    arun_frame k rVLo (bodyAfterClauseTwo c) (by rfl) guarded
  rw [body_eq_clauseTwo_stages, arun_append, arun_append]
  exact hsuffix.trans hguard

/-! ## Size-independent counter folds -/

def ClauseOneStepSafe (c : R2Cfg) (k : Nat) (s : AState) : Prop :=
  let pre := beforeClauseOne c k s
  pre.regs 247 ≤ 1 ∧
    (pre.regs 247 = 1 →
      pre.regs rD + pre.regs rErr < M ∧
      pre.regs rD + pre.regs rErr + pre.regs rNe < M ∧
      biasOf c.sc + pre.regs rThr < M)

def ClauseTwoStepSafe (c : R2Cfg) (k : Nat) (s : AState) : Prop :=
  let pre := beforeClauseTwo c k s
  pre.regs 247 ≤ 1 ∧
    (pre.regs 247 = 1 →
      pre.regs rD + pre.regs rThr < M ∧
      biasOf c.sc + pre.regs rErr < M)

def AllClauseOneSafe (c : R2Cfg) : AState → List Nat → Prop
  | _, [] => True
  | s, k :: ks => ClauseOneStepSafe c k s ∧
      AllClauseOneSafe c (arun k s c.body) ks

def AllClauseTwoSafe (c : R2Cfg) : AState → List Nat → Prop
  | _, [] => True
  | s, k :: ks => ClauseTwoStepSafe c k s ∧
      AllClauseTwoSafe c (arun k s c.body) ks

theorem allClauseOneSafe_append (c : R2Cfg) (s : AState)
    (xs ys : List Nat) :
    AllClauseOneSafe c s (xs ++ ys) ↔
      AllClauseOneSafe c s xs ∧
        AllClauseOneSafe c
          (xs.foldl (fun st k => arun k st c.body) s) ys := by
  induction xs generalizing s with
  | nil => simp [AllClauseOneSafe]
  | cons k ks ih =>
      simp only [List.cons_append, AllClauseOneSafe, List.foldl_cons]
      rw [ih]
      constructor
      · rintro ⟨hstep, hrest, htail⟩
        exact ⟨⟨hstep, hrest⟩, htail⟩
      · rintro ⟨⟨hstep, hrest⟩, htail⟩
        exact ⟨hstep, hrest, htail⟩

theorem allClauseTwoSafe_append (c : R2Cfg) (s : AState)
    (xs ys : List Nat) :
    AllClauseTwoSafe c s (xs ++ ys) ↔
      AllClauseTwoSafe c s xs ∧
        AllClauseTwoSafe c
          (xs.foldl (fun st k => arun k st c.body) s) ys := by
  induction xs generalizing s with
  | nil => simp [AllClauseTwoSafe]
  | cons k ks ih =>
      simp only [List.cons_append, AllClauseTwoSafe, List.foldl_cons]
      rw [ih]
      constructor
      · rintro ⟨hstep, hrest, htail⟩
        exact ⟨⟨hstep, hrest⟩, htail⟩
      · rintro ⟨⟨hstep, hrest⟩, htail⟩
        exact ⟨hstep, hrest, htail⟩

theorem body_vup_increment_safe (c : R2Cfg) (k : Nat) (s : AState)
    (hsafe : ClauseOneStepSafe c k s)
    (hroom :
      let pre := beforeClauseOne c k s
      s.regs rVUp + clauseOneFailure c.sc (pre.regs rD)
        (pre.regs rErr) (pre.regs rNe) (pre.regs rThr)
        (pre.regs 247) < M) :
    let pre := beforeClauseOne c k s
    (arun k s c.body).regs rVUp =
      s.regs rVUp + clauseOneFailure c.sc (pre.regs rD)
        (pre.regs rErr) (pre.regs rNe) (pre.regs rThr)
        (pre.regs 247) := by
  let pre := beforeClauseOne c k s
  change s.regs rVUp + clauseOneFailure c.sc (pre.regs rD)
    (pre.regs rErr) (pre.regs rNe) (pre.regs rThr) (pre.regs 247) < M at hroom
  change (arun k s c.body).regs rVUp =
    s.regs rVUp + clauseOneFailure c.sc (pre.regs rD)
      (pre.regs rErr) (pre.regs rNe) (pre.regs rThr) (pre.regs 247)
  change pre.regs 247 ≤ 1 ∧
    (pre.regs 247 = 1 →
      pre.regs rD + pre.regs rErr < M ∧
      pre.regs rD + pre.regs rErr + pre.regs rNe < M ∧
      biasOf c.sc + pre.regs rThr < M) at hsafe
  have hfin : pre.regs 247 = 0 ∨ pre.regs 247 = 1 := by
    omega
  rcases hfin with hzero | hone
  · have hbit : clauseOneFailure c.sc (pre.regs rD) (pre.regs rErr)
        (pre.regs rNe) (pre.regs rThr) (pre.regs 247) = 0 := by
      simp [clauseOneFailure, hzero]
    have hupM : s.regs rVUp < M := by simpa only [hbit, Nat.add_zero] using hroom
    have hrun := body_vup_increment_nonfinal c k s hzero hupM
    simpa only [hbit, Nat.add_zero] using hrun
  · have hfits := hsafe.2 hone
    exact body_vup_increment c k s hfits.1 hfits.2.1 hfits.2.2 hroom

theorem body_vlo_increment_safe (c : R2Cfg) (k : Nat) (s : AState)
    (hsafe : ClauseTwoStepSafe c k s)
    (hroom :
      let pre := beforeClauseTwo c k s
      s.regs rVLo + clauseTwoFailure c.sc (pre.regs rD)
        (pre.regs rErr) (pre.regs rThr) (pre.regs 247) < M) :
    let pre := beforeClauseTwo c k s
    (arun k s c.body).regs rVLo =
      s.regs rVLo + clauseTwoFailure c.sc (pre.regs rD)
        (pre.regs rErr) (pre.regs rThr) (pre.regs 247) := by
  let pre := beforeClauseTwo c k s
  change s.regs rVLo + clauseTwoFailure c.sc (pre.regs rD)
    (pre.regs rErr) (pre.regs rThr) (pre.regs 247) < M at hroom
  change (arun k s c.body).regs rVLo =
    s.regs rVLo + clauseTwoFailure c.sc (pre.regs rD)
      (pre.regs rErr) (pre.regs rThr) (pre.regs 247)
  change pre.regs 247 ≤ 1 ∧
    (pre.regs 247 = 1 →
      pre.regs rD + pre.regs rThr < M ∧
      biasOf c.sc + pre.regs rErr < M) at hsafe
  have hfin : pre.regs 247 = 0 ∨ pre.regs 247 = 1 := by
    omega
  rcases hfin with hzero | hone
  · have hbit : clauseTwoFailure c.sc (pre.regs rD) (pre.regs rErr)
        (pre.regs rThr) (pre.regs 247) = 0 := by
      simp [clauseTwoFailure, hzero]
    have hloM : s.regs rVLo < M := by simpa only [hbit, Nat.add_zero] using hroom
    have hrun := body_vlo_increment_nonfinal c k s hzero hloM
    simpa only [hbit, Nat.add_zero] using hrun
  · have hfits := hsafe.2 hone
    exact body_vlo_increment c k s hfits.1 hfits.2 hroom

/-- Under the local word-safety facts, the upper-clause counter is monotone
and grows by at most one per scheduled body. -/
theorem foldl_body_vup_bounds (c : R2Cfg) (indices : List Nat) (s : AState)
    (hsafe : AllClauseOneSafe c s indices)
    (hroom : s.regs rVUp + indices.length < M) :
    let out := indices.foldl (fun st k => arun k st c.body) s
    s.regs rVUp ≤ out.regs rVUp ∧
      out.regs rVUp ≤ s.regs rVUp + indices.length := by
  induction indices generalizing s with
  | nil => simp
  | cons k ks ih =>
      simp only [AllClauseOneSafe] at hsafe
      let pre := beforeClauseOne c k s
      let bit := clauseOneFailure c.sc (pre.regs rD) (pre.regs rErr)
        (pre.regs rNe) (pre.regs rThr) (pre.regs 247)
      have hbit : bit ≤ 1 :=
        Nat.le_trans (clauseOneFailure_le_fin c.sc _ _ _ _ _)
          hsafe.1.1
      have hfirstRoom : s.regs rVUp + bit < M := by
        simp only [List.length_cons] at hroom
        omega
      have hfirst := body_vup_increment_safe c k s hsafe.1 hfirstRoom
      change (arun k s c.body).regs rVUp = s.regs rVUp + bit at hfirst
      have htailRoom :
          (arun k s c.body).regs rVUp + ks.length < M := by
        rw [hfirst]
        simp only [List.length_cons] at hroom
        omega
      have htail := ih (s := arun k s c.body) hsafe.2 htailRoom
      dsimp only at htail
      simp only [List.foldl]
      constructor
      · calc
          s.regs rVUp ≤ s.regs rVUp + bit := Nat.le_add_right _ _
          _ = (arun k s c.body).regs rVUp := hfirst.symm
          _ ≤ _ := htail.1
      · calc
          (ks.foldl (fun st k => arun k st c.body)
              (arun k s c.body)).regs rVUp
              ≤ (arun k s c.body).regs rVUp + ks.length := htail.2
          _ = s.regs rVUp + bit + ks.length := by rw [hfirst]
          _ ≤ s.regs rVUp + (ks.length + 1) := by omega

/-- Lower-clause counterpart of `foldl_body_vup_bounds`. -/
theorem foldl_body_vlo_bounds (c : R2Cfg) (indices : List Nat) (s : AState)
    (hsafe : AllClauseTwoSafe c s indices)
    (hroom : s.regs rVLo + indices.length < M) :
    let out := indices.foldl (fun st k => arun k st c.body) s
    s.regs rVLo ≤ out.regs rVLo ∧
      out.regs rVLo ≤ s.regs rVLo + indices.length := by
  induction indices generalizing s with
  | nil => simp
  | cons k ks ih =>
      simp only [AllClauseTwoSafe] at hsafe
      let pre := beforeClauseTwo c k s
      let bit := clauseTwoFailure c.sc (pre.regs rD) (pre.regs rErr)
        (pre.regs rThr) (pre.regs 247)
      have hbit : bit ≤ 1 :=
        Nat.le_trans (clauseTwoFailure_le_fin c.sc _ _ _ _)
          hsafe.1.1
      have hfirstRoom : s.regs rVLo + bit < M := by
        simp only [List.length_cons] at hroom
        omega
      have hfirst := body_vlo_increment_safe c k s hsafe.1 hfirstRoom
      change (arun k s c.body).regs rVLo = s.regs rVLo + bit at hfirst
      have htailRoom :
          (arun k s c.body).regs rVLo + ks.length < M := by
        rw [hfirst]
        simp only [List.length_cons] at hroom
        omega
      have htail := ih (s := arun k s c.body) hsafe.2 htailRoom
      dsimp only at htail
      simp only [List.foldl]
      constructor
      · calc
          s.regs rVLo ≤ s.regs rVLo + bit := Nat.le_add_right _ _
          _ = (arun k s c.body).regs rVLo := hfirst.symm
          _ ≤ _ := htail.1
      · calc
          (ks.foldl (fun st k => arun k st c.body)
              (arun k s c.body)).regs rVLo
              ≤ (arun k s c.body).regs rVLo + ks.length := htail.2
          _ = s.regs rVLo + bit + ks.length := by rw [hfirst]
          _ ≤ s.regs rVLo + (ks.length + 1) := by omega

def clauseBodyPrefix (c : R2Cfg) (entry : AState) (j : Nat) : AState :=
  (List.range j).foldl (fun s index => arun index s c.body) entry

def clauseOneAt (c : R2Cfg) (entry : AState) (j : Nat) : Nat :=
  let pre := beforeClauseOne c j (clauseBodyPrefix c entry j)
  clauseOneFailure c.sc (pre.regs rD) (pre.regs rErr) (pre.regs rNe)
    (pre.regs rThr) (pre.regs 247)

def clauseTwoAt (c : R2Cfg) (entry : AState) (j : Nat) : Nat :=
  let pre := beforeClauseTwo c j (clauseBodyPrefix c entry j)
  clauseTwoFailure c.sc (pre.regs rD) (pre.regs rErr) (pre.regs rThr)
    (pre.regs 247)

/-- A terminal zero upper counter forces every dynamic upper-clause bit to
zero, provided only the symbolic local word-safety predicate. -/
theorem every_clauseOne_passes_of_zero (c : R2Cfg) (entry : AState) (N : Nat)
    (hsafe : AllClauseOneSafe c entry (List.range N))
    (hentry : entry.regs rVUp = 0) (hNM : N < M)
    (hfinal : ((List.range N).foldl
      (fun s index => arun index s c.body) entry).regs rVUp = 0) :
    ∀ j, j < N → clauseOneAt c entry j = 0 := by
  intro j hj
  let pre := clauseBodyPrefix c entry j
  let bit := clauseOneAt c entry j
  let after := arun j pre c.body
  let tailLen := N - (j + 1)
  let tail := List.range' (j + 1) tailLen
  have hcount : N = (j + 1) + tailLen := by
    dsimp only [tailLen]
    omega
  have hrange : List.range N = List.range j ++ j :: tail := by
    rw [hcount, List.range_eq_range',
      ← List.range'_append_1 (s := 0) (m := j + 1) (n := tailLen),
      List.range'_1_concat, ← List.range_eq_range']
    simp only [Nat.zero_add, List.append_assoc, List.singleton_append, tail]
  have hsafeSplit := (allClauseOneSafe_append c entry
    (List.range j) (j :: tail)).mp (by simpa only [hrange] using hsafe)
  have hsafeStep : ClauseOneStepSafe c j pre := by
    simpa only [AllClauseOneSafe, pre, clauseBodyPrefix] using hsafeSplit.2.1
  have hsafeTail : AllClauseOneSafe c after tail := by
    simpa only [AllClauseOneSafe, after, pre, clauseBodyPrefix] using
      hsafeSplit.2.2
  have hpreBounds := foldl_body_vup_bounds c (List.range j) entry
    hsafeSplit.1 (by rw [hentry]; simp only [List.length_range, Nat.zero_add]; omega)
  have hpreLe : pre.regs rVUp ≤ j := by
    simpa only [pre, clauseBodyPrefix, List.length_range, hentry,
      Nat.zero_add] using hpreBounds.2
  have hbitLe : bit ≤ 1 := by
    dsimp only [bit, clauseOneAt]
    exact Nat.le_trans (clauseOneFailure_le_fin c.sc _ _ _ _ _)
      hsafeStep.1
  have hfirstRoom : pre.regs rVUp + bit < M := by omega
  have hfirst := body_vup_increment_safe c j pre hsafeStep hfirstRoom
  change after.regs rVUp = pre.regs rVUp + bit at hfirst
  have htailRoom : after.regs rVUp + tail.length < M := by
    rw [hfirst]
    have htailLength : tail.length = tailLen := by simp [tail]
    rw [htailLength]
    omega
  have htailBounds := foldl_body_vup_bounds c tail after hsafeTail htailRoom
  dsimp only at htailBounds
  have hfinal' :
      (tail.foldl (fun s index => arun index s c.body) after).regs rVUp = 0 := by
    rw [hrange, List.foldl_append] at hfinal
    simpa only [List.foldl_cons, List.foldl_nil, pre, after,
      clauseBodyPrefix] using hfinal
  have hafterZero : after.regs rVUp = 0 := by omega
  omega

/-- Lower-clause counterpart of `every_clauseOne_passes_of_zero`. -/
theorem every_clauseTwo_passes_of_zero (c : R2Cfg) (entry : AState) (N : Nat)
    (hsafe : AllClauseTwoSafe c entry (List.range N))
    (hentry : entry.regs rVLo = 0) (hNM : N < M)
    (hfinal : ((List.range N).foldl
      (fun s index => arun index s c.body) entry).regs rVLo = 0) :
    ∀ j, j < N → clauseTwoAt c entry j = 0 := by
  intro j hj
  let pre := clauseBodyPrefix c entry j
  let bit := clauseTwoAt c entry j
  let after := arun j pre c.body
  let tailLen := N - (j + 1)
  let tail := List.range' (j + 1) tailLen
  have hcount : N = (j + 1) + tailLen := by
    dsimp only [tailLen]
    omega
  have hrange : List.range N = List.range j ++ j :: tail := by
    rw [hcount, List.range_eq_range',
      ← List.range'_append_1 (s := 0) (m := j + 1) (n := tailLen),
      List.range'_1_concat, ← List.range_eq_range']
    simp only [Nat.zero_add, List.append_assoc, List.singleton_append, tail]
  have hsafeSplit := (allClauseTwoSafe_append c entry
    (List.range j) (j :: tail)).mp (by simpa only [hrange] using hsafe)
  have hsafeStep : ClauseTwoStepSafe c j pre := by
    simpa only [AllClauseTwoSafe, pre, clauseBodyPrefix] using hsafeSplit.2.1
  have hsafeTail : AllClauseTwoSafe c after tail := by
    simpa only [AllClauseTwoSafe, after, pre, clauseBodyPrefix] using
      hsafeSplit.2.2
  have hpreBounds := foldl_body_vlo_bounds c (List.range j) entry
    hsafeSplit.1 (by rw [hentry]; simp only [List.length_range, Nat.zero_add]; omega)
  have hpreLe : pre.regs rVLo ≤ j := by
    simpa only [pre, clauseBodyPrefix, List.length_range, hentry,
      Nat.zero_add] using hpreBounds.2
  have hbitLe : bit ≤ 1 := by
    dsimp only [bit, clauseTwoAt]
    exact Nat.le_trans (clauseTwoFailure_le_fin c.sc _ _ _ _)
      hsafeStep.1
  have hfirstRoom : pre.regs rVLo + bit < M := by omega
  have hfirst := body_vlo_increment_safe c j pre hsafeStep hfirstRoom
  change after.regs rVLo = pre.regs rVLo + bit at hfirst
  have htailRoom : after.regs rVLo + tail.length < M := by
    rw [hfirst]
    have htailLength : tail.length = tailLen := by simp [tail]
    rw [htailLength]
    omega
  have htailBounds := foldl_body_vlo_bounds c tail after hsafeTail htailRoom
  dsimp only at htailBounds
  have hfinal' :
      (tail.foldl (fun s index => arun index s c.body) after).regs rVLo = 0 := by
    rw [hrange, List.foldl_append] at hfinal
    simpa only [List.foldl_cons, List.foldl_nil, pre, after,
      clauseBodyPrefix] using hfinal
  have hafterZero : after.regs rVLo = 0 := by omega
  omega

/-- The retained production receipt projects to zero upper/lower counters at
the exact loop output. -/
theorem runtimeProduction_verified_no_clause_failure :
    runtimeProductionLoopOut.regs rVUp = 0 ∧
      runtimeProductionLoopOut.regs rVLo = 0 := by
  rcases runtimeProduction_verified_failure_classes_zero with ⟨_hv, hs⟩
  have hup := hs 0 (by decide)
  have hlo := hs 1 (by decide)
  have hgetUp : violRegs.get ⟨0, by decide⟩ = rVUp := by rfl
  have hgetLo : violRegs.get ⟨1, by decide⟩ = rVLo := by rfl
  rw [hgetUp] at hup
  rw [hgetLo] at hlo
  have frame (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
          (epilogueTestPrefix runtimeProductionCfg) = false) :
      runtimeProductionTested.regs r = runtimeProductionLoopOut.regs r := by
    rw [runtimeProductionTested]
    exact arun_frame 0 r (epilogueTestPrefix runtimeProductionCfg)
      h runtimeProductionLoopOut
  have hframeUp := frame rVUp (by rfl)
  have hframeLo := frame rVLo (by rfl)
  exact ⟨hframeUp.symm.trans hup, hframeLo.symm.trans hlo⟩

#print axioms logClauseOneInstrs_vup_run
#print axioms logClauseOneBody_vup_run
#print axioms logClauseTwoInstrs_vlo_run
#print axioms logClauseTwoBody_vlo_run
#print axioms body_vup_increment
#print axioms body_vlo_increment
#print axioms foldl_body_vup_bounds
#print axioms foldl_body_vlo_bounds
#print axioms every_clauseOne_passes_of_zero
#print axioms every_clauseTwo_passes_of_zero
#print axioms runtimeProduction_verified_no_clause_failure

end LeanCompCert.Ports.R2SegSieve
