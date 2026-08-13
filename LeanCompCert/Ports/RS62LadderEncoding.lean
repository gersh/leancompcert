import LeanCompCert.Ports.RS62LadderProgram
import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Verified.Frontend
import LeanCompCert.Verified.BlockDefined

/-!
# What `RS62LadderProgram` denotes

`Ports/RS62LadderProgram.lean` proves that the emitted C computes
`AProgram.denote`, and then says, plainly, what it does **not** prove:

> **Not proved here**: that `AProgram.denote` *is* the ladder … That is the
> encoding obligation, it is stated below as `LadderEncoding`, and it is the
> step neither the artifact nor `evidenced_decide` touches.

This file discharges that obligation for `scanPrime`.  The proof is symbolic:
it composes block semantics, reblocks the flat rounds, and checks a compact
word-room premise.  It never evaluates a production candidate range.

## 1. The index-restricted fold bridge — proved

`Verified/FoldBridge.lean` quantifies its body-simulation hypothesis over
**every** index.  The ladder body cannot satisfy that: at an adversarial index
the decoded candidate `n₀ + i / B` wraps modulo `2⁶⁴`, `m = n − 1` becomes `0`,
and the `udiv` by `m` is genuinely undefined — `denoteOp .udiv _ 0 = none`.

`Program.denote_eq_foldl_mem` is `FoldBridge.Program.denote_eq_foldl` with the
hypothesis restricted to `index < p.loopCount`, which is all `List.range`
supplies.  It is proved by the same simulation argument, is size-independent
in the same way, and is reusable by **any** port whose body contains a partial
operation.  `foldlM_body_eq_foldl_mem` and `foldl_obs_mem` are its two layers.

## 2. All three instruction blocks — proved

`decodeBlock_denote` and `scanBlock_denote` show that those blocks denote a
transparent state function, with the `% M` truncations of the 64-bit machine
left in.  Keeping the truncations is deliberate and is the house pattern of
`Ports/MobiusResidueModel.lean`: a model that already tells the truth at every
index has to say what the machine does, not what the mathematics wants.  The
interpretation step comes second, under range hypotheses, so that no proof has
to do both at once.

`commitBlock` — the third and largest block, thirty-two instructions carrying
seven `udiv` guards — is proved defined by `commitBlock_defined`.  Its lower
and upper circuits are proved equal to `incLWord` and `incUWord`, and
`commitBlock_denote_vals` proves the exact prime gate, accumulator additions,
and reset.  Every proof is block-sized; none evaluates a candidate range.

## 3. Complete encoding

`ladderBody_denote_flatRound` composes all three instruction blocks.
`flatObs_fold_eq_loopE` reblocks every flat round into candidate steps.
`ladderFold_denote` lifts those equations through the partial machine
semantics, and `ladderEncoding_scanPrime` closes the public encoding
obligation.  `FlatRoom` remains an explicit, compiled-checkable premise so
machine-word transparency is never obtained from wraparound.

## Trust, stated exactly

Nothing here is itself a production run certificate.  The encoding theorem is
proved from ordinary Lean foundations; a run admission still needs a compiled
campaign, its word-room receipt, and the source-predicate bridge.
-/

namespace LeanCompCert.Ports.RS62LadderEncoding

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Ports.RS62
open LeanCompCert.Ports.RS62Ladder

/-! ## The index-restricted fold bridge -/

/--
**Body simulation, at the indices the loop visits.**

`Verified.FoldBridge.foldlM_body_eq_foldl` with the simulation hypothesis
restricted by a predicate `Q` on the index.  A body containing a partial
operation — a `udiv` whose divisor is decoded from the index — cannot satisfy
the unrestricted form, and this is the weakest strengthening that admits it.
-/
theorem foldlM_body_eq_foldl_mem
    (body : List Instr) (Q : Nat → Prop) (P : RegState → Prop)
    (step : Nat → RegState → RegState)
    (hStep : ∀ index s, Q index → P s →
      denoteInstrs index s body = some (step index s))
    (hClosed : ∀ index s, Q index → P s → P (step index s)) :
    ∀ (indices : List Nat), (∀ i ∈ indices, Q i) → ∀ s : RegState, P s →
      indices.foldlM (fun s index => denoteInstrs index s body) s =
        some (indices.foldl (fun s index => step index s) s) := by
  intro indices
  induction indices with
  | nil => intro _ s _; rfl
  | cons index rest ih =>
      intro hQ s hP
      have hQi : Q index := hQ index (by simp)
      show (denoteInstrs index s body).bind
        (fun s => rest.foldlM (fun s index => denoteInstrs index s body) s) = _
      rw [hStep index s hQi hP]
      exact ih (fun i hi => hQ i (by simp [hi])) (step index s)
        (hClosed index s hQi hP)

/-- **Observation transfer**, at the indices the loop visits. -/
theorem foldl_obs_mem {A : Type _}
    (Q : Nat → Prop) (P : RegState → Prop) (step : Nat → RegState → RegState)
    (obs : RegState → A) (g : Nat → A → A)
    (hClosed : ∀ index s, Q index → P s → P (step index s))
    (hObs : ∀ index s, Q index → P s → obs (step index s) = g index (obs s)) :
    ∀ (indices : List Nat), (∀ i ∈ indices, Q i) → ∀ s : RegState, P s →
      obs (indices.foldl (fun s index => step index s) s) =
        indices.foldl (fun acc index => g index acc) (obs s) := by
  intro indices
  induction indices with
  | nil => intro _ s _; rfl
  | cons index rest ih =>
      intro hQ s hP
      have hQi : Q index := hQ index (by simp)
      show obs (rest.foldl (fun s index => step index s) (step index s)) = _
      rw [ih (fun i hi => hQ i (by simp [hi])) (step index s)
          (hClosed index s hQi hP), hObs index s hQi hP]
      rfl

/--
**The range-loop bridge, index-restricted.**

Identical to `FoldBridge.Program.denote_eq_foldl` except that the body only
has to simulate `step` at indices below `p.loopCount` — the ones
`List.range p.loopCount` contains.
-/
theorem Program.denote_eq_foldl_mem
    (p : Program) (P : RegState → Prop) (step : Nat → RegState → RegState)
    (fin : RegState → RegState) (s₀ : RegState)
    (hInit : denoteInstrs 0 initialState p.init = some s₀)
    (hP₀ : P s₀)
    (hStep : ∀ index s, index < p.loopCount → P s →
      denoteInstrs index s p.body = some (step index s))
    (hClosed : ∀ index s, index < p.loopCount → P s → P (step index s))
    (hEpilogue : ∀ s, P s → denoteInstrs 0 s p.epilogue = some (fin s)) :
    p.denote =
      some (fin ((List.range p.loopCount).foldl
        (fun s index => step index s) s₀) p.output) := by
  have hmem : ∀ i ∈ List.range p.loopCount, i < p.loopCount := by
    intro i hi; exact List.mem_range.mp hi
  have hFoldP : P ((List.range p.loopCount).foldl
      (fun s index => step index s) s₀) := by
    clear hInit
    revert hP₀
    have : ∀ (l : List Nat), (∀ i ∈ l, i < p.loopCount) → ∀ s, P s →
        P (l.foldl (fun s index => step index s) s) := by
      intro l
      induction l with
      | nil => intro _ s h; exact h
      | cons i rest ih =>
          intro hQ s hP
          exact ih (fun j hj => hQ j (by simp [hj])) (step i s)
            (hClosed i s (hQ i (by simp)) hP)
    exact this (List.range p.loopCount) hmem s₀
  show (denoteInstrs 0 initialState p.init).bind _ = _
  rw [hInit]
  show ((List.range p.loopCount).foldlM
    (fun s index => denoteInstrs index s p.body) s₀).bind _ = _
  rw [foldlM_body_eq_foldl_mem p.body (fun i => i < p.loopCount) P step
    hStep hClosed (List.range p.loopCount) hmem s₀ hP₀]
  show ((denoteInstrs 0 _ p.epilogue).bind _) = _
  rw [hEpilogue _ hFoldP]
  rfl

/-! ## The machine model, one instruction block at a time

Each `def` below is the transcription of one block of `ladderBody`, every
`% M` truncation included, and each lemma says that the block denotes it.
Reads are of the *incoming* state, so the three compose by
`Frontend.denoteInstrs_append`.
-/

/-- `decodeBlock` transcribed: the round, the candidate, the trial divisor. -/
def dstep (n0 B i : Nat) (s : RegState) : RegState :=
  (((s.set rR (i % M % (B % M) % M)).set rN (i % M / (B % M) % M)).set rN
      ((i % M / (B % M) % M + n0 % M) % M)).set rD
      ((i % M % (B % M) % M + 2 % M) % M)

theorem decodeBlock_denote (n0 B i : Nat) (s : RegState) (hB : B % M ≠ 0) :
    denoteInstrs i s (decodeBlock n0 B) = some (dstep n0 B i s) := by
  simp [decodeBlock, denoteInstrs, denoteInstr, denoteOperand, denoteOp,
    dstep, hB, RegState.set, rR, rN, rD]

/-- Decode values and the three carried registers, with every machine modulus
made transparent by scalar range premises. -/
theorem dstep_vals (n0 B i : Nat) (s : RegState)
    (hiM : i < M) (hBM : B < M) (hB0 : 0 < B)
    (hnM : n0 + i / B < M) (hdM : i % B + 2 < M) :
    dstep n0 B i s rR = i % B ∧
    dstep n0 B i s rN = n0 + i / B ∧
    dstep n0 B i s rD = i % B + 2 ∧
    dstep n0 B i s rSL = s rSL ∧
    dstep n0 B i s rSU = s rSU ∧
    dstep n0 B i s rAcc = s rAcc := by
  have hremB : i % B < B := Nat.mod_lt _ hB0
  have hremM : i % B < M := Nat.lt_trans hremB hBM
  have hdivM : i / B < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self i B) hiM
  simp [dstep, RegState.set, rR, rN, rD, rSL, rSU, rAcc,
    Nat.mod_eq_of_lt hiM, Nat.mod_eq_of_lt hBM,
    Nat.mod_eq_of_lt hremM, Nat.mod_eq_of_lt hdivM,
    Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hdM, Nat.add_comm]

/-- One named instruction step, keeping the preceding state opaque. -/
private theorem step_write {k d : Nat} {s : RegState} {p q : List Instr}
    {op : Op} {l r : Operand} (hq : q = p ++ [Instr.binop d op l r])
    {a b v : Nat} (hl : denoteOperand k (srun k s p) l = a)
    (hr : denoteOperand k (srun k s p) r = b)
    (hop : denoteOp op a b = some v) : srun k s q d = v := by
  rw [hq, srun_read_last k d p _ rfl]
  exact sval_binop_val hl hr hop

/-- Compose three successful blocks without unfolding any of their
instructions. -/
private theorem denoteInstrs_three_some (k : Nat) (s0 s1 s2 s3 : RegState)
    (xs ys zs : List Instr)
    (h1 : denoteInstrs k s0 xs = some s1)
    (h2 : denoteInstrs k s1 ys = some s2)
    (h3 : denoteInstrs k s2 zs = some s3) :
    denoteInstrs k s0 ((xs ++ ys) ++ zs) = some s3 := by
  rw [Frontend.denoteInstrs_append, Frontend.denoteInstrs_append, h1]
  simp only [Option.bind_some, h2, h3]

/-- `scanBlock` transcribed: one `spfStep` round on the found-mask. -/
def sstep (i : Nat) (s : RegState) : RegState :=
  (denoteInstrs i s scanBlock).getD s

private def sc0 : Instr := .binop rG .eq (.reg rAcc) (.lit 0)
private def sc1 : Instr := .binop rT1 .mul (.reg rD) (.reg rD)
private def sc2 : Instr := .binop rT1 .le (.reg rT1) (.reg rN)
private def sc3 : Instr := .binop rG .mul (.reg rG) (.reg rT1)
private def sc4 : Instr := .binop rT2 .urem (.reg rN) (.reg rD)
private def sc5 : Instr := .binop rT2 .eq (.reg rT2) (.lit 0)
private def sc6 : Instr := .binop rG .mul (.reg rG) (.reg rT2)
private def sc7 : Instr := .binop rT1 .sub (.lit 1) (.reg rG)
private def sc8 : Instr := .binop rT1 .mul (.reg rT1) (.reg rAcc)
private def sc9 : Instr := .binop rT2 .mul (.reg rG) (.reg rD)
private def sc10 : Instr := .binop rAcc .add (.reg rT1) (.reg rT2)

private def sp1 : List Instr := [sc0]
private def sp2 : List Instr := sp1 ++ [sc1]
private def sp3 : List Instr := sp2 ++ [sc2]
private def sp4 : List Instr := sp3 ++ [sc3]
private def sp5 : List Instr := sp4 ++ [sc4]
private def sp6 : List Instr := sp5 ++ [sc5]
private def sp7 : List Instr := sp6 ++ [sc6]
private def sp8 : List Instr := sp7 ++ [sc7]
private def sp9 : List Instr := sp8 ++ [sc8]
private def sp10 : List Instr := sp9 ++ [sc9]
private def sp11 : List Instr := sp10 ++ [sc10]

private theorem scanBlock_eq_sp11 : scanBlock = sp11 := rfl

/-- The scan's sole partial operation is the remainder by the decoded divisor.
The proof retires the four-instruction prefix and six-instruction suffix as
opaque division-free stages. -/
theorem scanBlock_defined (i : Nat) (s : RegState) (hD : s rD ≠ 0) :
    SAllDefined i s scanBlock := by
  rw [scanBlock_eq_sp11]
  show SAllDefined i s (sp4 ++ sc4 :: [sc5, sc6, sc7, sc8, sc9, sc10])
  refine sAllDefined_stage (by rfl) (sDefined_urem ?_)
    (sAllDefined_of_noDiv i _ _ (by rfl))
  rw [denoteOperand_reg, srun_frame i rD sp4 (by rfl)]
  exact hD

theorem scanBlock_denote (i : Nat) (s : RegState) (hD : s rD ≠ 0) :
    denoteInstrs i s scanBlock = some (sstep i s) := by
  have hrun := denoteInstrs_eq_srun i scanBlock s (scanBlock_defined i s hD)
  unfold sstep
  rw [hrun]
  rfl

/-- Exact accumulator observation for one fixed-shape factor-scan round.
This is an eleven-instruction symbolic walk, not an evaluation of `spfScan`. -/
theorem scanBlock_srun_rAcc (i : Nat) (s : RegState) (a n d : Nat)
    (ha : s rAcc = a) (hn : s rN = n) (hd : s rD = d)
    (haM : a < M) (hnM : n < M) (hdM : d < M)
    (hddM : d * d < M) (hd0 : d ≠ 0) :
    srun i s scanBlock rAcc =
      if a = 0 ∧ d * d ≤ n ∧ n % d = 0 then d else a := by
  have e0 : srun i s sp1 rG = if a = 0 then 1 else 0 := by
    apply step_write (q := sp1) (p := []) (op := .eq)
      (l := .reg rAcc) (r := .lit 0) (a := a) (b := 0)
      (v := if a = 0 then 1 else 0) (by rfl)
    · rw [denoteOperand_reg]
      exact ha
    · exact denoteOperand_lit_of_lt i _ (by decide)
    · exact denoteOp_eq_val _ _
  have e1 : srun i s sp2 rT1 = d * d := by
    apply step_write (q := sp2) (p := sp1) (by rfl)
    · rw [denoteOperand_reg, srun_frame i rD sp1 (by rfl), hd]
    · rw [denoteOperand_reg, srun_frame i rD sp1 (by rfl), hd]
    · exact denoteOp_mul_of_lt hddM
  have e2 : srun i s sp3 rT1 = if d * d ≤ n then 1 else 0 := by
    apply step_write (q := sp3) (p := sp2) (by rfl)
    · rw [denoteOperand_reg, e1]
    · rw [denoteOperand_reg, srun_frame i rN sp2 (by rfl), hn]
    · exact denoteOp_le_val _ _
  have e3 : srun i s sp4 rG =
      if a = 0 ∧ d * d ≤ n then 1 else 0 := by
    apply step_write (q := sp4) (p := sp3) (by rfl)
    · rw [denoteOperand_reg,
        show sp3 = sp1 ++ [sc1, sc2] from rfl,
        srun_frame_append i rG sp1 [sc1, sc2] (by rfl), e0]
    · rw [denoteOperand_reg, e2]
    · by_cases h0 : a = 0 <;> by_cases hle : d * d ≤ n <;>
        simp [h0, hle, denoteOp, Nat.mod_eq_of_lt (by decide : 1 < M)]
  have e4 : srun i s sp5 rT2 = n % d := by
    apply step_write (q := sp5) (p := sp4) (by rfl)
    · rw [denoteOperand_reg, srun_frame i rN sp4 (by rfl), hn]
    · rw [denoteOperand_reg, srun_frame i rD sp4 (by rfl), hd]
    · exact denoteOp_urem_of_ne hd0 hnM
  have e5 : srun i s sp6 rT2 = if n % d = 0 then 1 else 0 := by
    apply step_write (q := sp6) (p := sp5) (by rfl)
    · rw [denoteOperand_reg, e4]
    · exact denoteOperand_lit_of_lt i _ (by decide)
    · exact denoteOp_eq_val _ _
  have e6 : srun i s sp7 rG =
      if a = 0 ∧ d * d ≤ n ∧ n % d = 0 then 1 else 0 := by
    apply step_write (q := sp7) (p := sp6) (by rfl)
    · rw [denoteOperand_reg,
        show sp6 = sp4 ++ [sc4, sc5] from rfl,
        srun_frame_append i rG sp4 [sc4, sc5] (by rfl), e3]
    · rw [denoteOperand_reg, e5]
    · by_cases h0 : a = 0 <;> by_cases hle : d * d ≤ n <;>
        by_cases hmod : n % d = 0 <;>
        simp [h0, hle, hmod, denoteOp, Nat.mod_eq_of_lt (by decide : 1 < M)]
  have e7 : srun i s sp8 rT1 =
      if a = 0 ∧ d * d ≤ n ∧ n % d = 0 then 0 else 1 := by
    apply step_write (q := sp8) (p := sp7) (by rfl)
    · exact denoteOperand_lit_of_lt i _ (by decide)
    · rw [denoteOperand_reg, e6]
    · by_cases hh : a = 0 ∧ d * d ≤ n ∧ n % d = 0
      · simpa [hh] using
          (denoteOp_sub_of_le (a := 1) (b := 1) (by decide) (by decide))
      · simpa [hh] using
          (denoteOp_sub_of_le (a := 1) (b := 0) (by decide) (by decide))
  have e8 : srun i s sp9 rT1 =
      if a = 0 ∧ d * d ≤ n ∧ n % d = 0 then 0 else a := by
    apply step_write (q := sp9) (p := sp8) (by rfl)
    · rw [denoteOperand_reg, e7]
    · rw [denoteOperand_reg, srun_frame i rAcc sp8 (by rfl), ha]
    · by_cases hh : a = 0 ∧ d * d ≤ n ∧ n % d = 0 <;>
        simp [hh, denoteOp, Nat.mod_eq_of_lt haM]
  have e9 : srun i s sp10 rT2 =
      if a = 0 ∧ d * d ≤ n ∧ n % d = 0 then d else 0 := by
    apply step_write (q := sp10) (p := sp9) (by rfl)
    · rw [denoteOperand_reg,
        show sp9 = sp7 ++ [sc7, sc8] from rfl,
        srun_frame_append i rG sp7 [sc7, sc8] (by rfl), e6]
    · rw [denoteOperand_reg, srun_frame i rD sp9 (by rfl), hd]
    · by_cases hh : a = 0 ∧ d * d ≤ n ∧ n % d = 0 <;>
        simp [hh, denoteOp, Nat.mod_eq_of_lt hdM]
  rw [scanBlock_eq_sp11]
  apply step_write (q := sp11) (p := sp10) (by rfl)
  · rw [denoteOperand_reg,
      show sp10 = sp9 ++ [sc9] from rfl,
      srun_frame_append i rT1 sp9 [sc9] (by rfl), e8]
  · rw [denoteOperand_reg, e9]
  · by_cases hh : a = 0 ∧ d * d ≤ n ∧ n % d = 0
    · simpa [hh] using (denoteOp_add_of_lt (show 0 + d < M by simpa using hdM))
    · simpa [hh] using (denoteOp_add_of_lt (show a + 0 < M by simpa using haM))

/-- The same observation on the partial denotation used by body composition. -/
theorem scanBlock_denote_vals (i : Nat) (s : RegState) (a n d : Nat)
    (ha : s rAcc = a) (hn : s rN = n) (hd : s rD = d)
    (haM : a < M) (hnM : n < M) (hdM : d < M)
    (hddM : d * d < M) (hd0 : d ≠ 0) :
    ∃ s', denoteInstrs i s scanBlock = some s' ∧
      s' rAcc = if a = 0 ∧ d * d ≤ n ∧ n % d = 0 then d else a := by
  refine ⟨srun i s scanBlock,
    denoteInstrs_eq_srun i scanBlock s (scanBlock_defined i s (by rw [hd]; exact hd0)),
    scanBlock_srun_rAcc i s a n d ha hn hd haM hnM hdM hddM hd0⟩

/-! ## The commit block is defined

The production loop is never evaluated here.  These lemmas inspect only the
three divisor-producing slices of each fixed straight-line increment block.
In particular, earlier states remain opaque `srun` terms; Lean never expands
the surrounding candidate fold or normalises an unrelated fixed-point
instruction.
-/

private def lDivM : Instr :=
  .binop rT2 .udiv (.lit (fpD - 1)) (.reg rM)
private def lDiv2M : Instr :=
  .binop rT1 .udiv (.reg rT1) (.reg rT2)
private def lDivM1 : Instr :=
  .binop rIL .udiv (.reg rT1) (.reg rT2)

private def lPreM : List Instr :=
  [ .binop rT1 .mul (.reg rM) (.lit 2)
  , .binop rT1 .add (.reg rT1) (.lit (3 * fpD)) ]
private def lPre2M : List Instr :=
  [ .binop rT1 .add (.reg rT1) (.reg rT2)
  , .binop rT2 .mul (.reg rM) (.lit 2) ]
private def lPreM1 : List Instr :=
  [ .binop rT1 .sub (.lit fpD) (.reg rT1)
  , .binop rT2 .sub (.reg rM) (.lit 1) ]

private theorem incLBlock_split :
    incLBlock = lPreM ++ lDivM :: (lPre2M ++ lDiv2M :: (lPreM1 ++ [lDivM1])) :=
  rfl

private def uDivM : Instr :=
  .binop rT2 .udiv (.reg rT2) (.reg rM)
private def uDiv2M : Instr :=
  .binop rT1 .udiv (.reg rT1) (.reg rT2)
private def uDivM1 : Instr :=
  .binop rIU .udiv (.reg rT1) (.reg rT2)

private def uPreM : List Instr :=
  [ .binop rT1 .mul (.reg rM) (.lit 2)
  , .binop rT1 .add (.reg rT1) (.lit (3 * fpD))
  , .binop rT2 .add (.reg rM) (.lit (3 * fpD))
  , .binop rT2 .sub (.reg rT2) (.lit 1) ]
private def uPre2M : List Instr :=
  [ .binop rT1 .sub (.reg rT1) (.reg rT2)
  , .binop rT2 .mul (.reg rM) (.lit 2) ]
private def uPreM1 : List Instr :=
  [ .binop rT2 .add (.reg rM) (.lit fpD)
  , .binop rT2 .sub (.reg rT2) (.lit 1)
  , .binop rT1 .sub (.reg rT2) (.reg rT1)
  , .binop rT2 .sub (.reg rM) (.lit 1) ]

private theorem incUBlock_split :
    incUBlock = uPreM ++ uDivM :: (uPre2M ++ uDiv2M :: (uPreM1 ++ [uDivM1])) :=
  rfl

private theorem two_m_srun (k : Nat) (u : RegState) (m : Nat)
    (hm : u rM = m) (h2m : 2 * m < M) :
    srun k u lPre2M rT2 = 2 * m := by
  rw [show lPre2M =
      [ .binop rT1 .add (.reg rT1) (.reg rT2) ] ++
        [ .binop rT2 .mul (.reg rM) (.lit 2) ] from rfl,
    srun_read_last k rT2 _ _ rfl]
  apply sval_binop_val
  · rw [denoteOperand_reg, srun_frame k rM _ (by rfl), hm]
  · exact denoteOperand_lit_of_lt k _ (by decide)
  · simpa [Nat.mul_comm] using
      (denoteOp_mul_of_lt (show m * 2 < M by omega))

private theorem two_m_srun_u (k : Nat) (u : RegState) (m : Nat)
    (hm : u rM = m) (h2m : 2 * m < M) :
    srun k u uPre2M rT2 = 2 * m := by
  rw [show uPre2M =
      [ .binop rT1 .sub (.reg rT1) (.reg rT2) ] ++
        [ .binop rT2 .mul (.reg rM) (.lit 2) ] from rfl,
    srun_read_last k rT2 _ _ rfl]
  apply sval_binop_val
  · rw [denoteOperand_reg, srun_frame k rM _ (by rfl), hm]
  · exact denoteOperand_lit_of_lt k _ (by decide)
  · simpa [Nat.mul_comm] using
      (denoteOp_mul_of_lt (show m * 2 < M by omega))

private theorem m_sub_one_srun (k : Nat) (u : RegState) (m : Nat)
    (hm : u rM = m) (hm2 : 2 ≤ m) (hmM : m < M) :
    srun k u lPreM1 rT2 = m - 1 := by
  rw [show lPreM1 =
      [ .binop rT1 .sub (.lit fpD) (.reg rT1) ] ++
        [ .binop rT2 .sub (.reg rM) (.lit 1) ] from rfl,
    srun_read_last k rT2 _ _ rfl]
  apply sval_binop_val
  · rw [denoteOperand_reg, srun_frame k rM _ (by rfl), hm]
  · exact denoteOperand_lit_of_lt k _ (by decide)
  · exact denoteOp_sub_of_le (by omega) hmM

private theorem m_sub_one_srun_u (k : Nat) (u : RegState) (m : Nat)
    (hm : u rM = m) (hm2 : 2 ≤ m) (hmM : m < M) :
    srun k u uPreM1 rT2 = m - 1 := by
  rw [show uPreM1 =
      [ .binop rT2 .add (.reg rM) (.lit fpD)
      , .binop rT2 .sub (.reg rT2) (.lit 1)
      , .binop rT1 .sub (.reg rT2) (.reg rT1) ] ++
        [ .binop rT2 .sub (.reg rM) (.lit 1) ] from rfl,
    srun_read_last k rT2 _ _ rfl]
  apply sval_binop_val
  · rw [denoteOperand_reg, srun_frame k rM _ (by rfl), hm]
  · exact denoteOperand_lit_of_lt k _ (by decide)
  · exact denoteOp_sub_of_le (by omega) hmM

private theorem incL_tail_m1_defined (k : Nat) (u : RegState) (m : Nat)
    (hm : u rM = m) (hm2 : 2 ≤ m) (hmM : m < M) :
    SAllDefined k u (lPreM1 ++ [lDivM1]) := by
  refine sAllDefined_stage (by rfl) (sDefined_udiv ?_)
    (sAllDefined_of_noDiv k _ _ (by rfl))
  rw [denoteOperand_reg, m_sub_one_srun k u m hm hm2 hmM]
  omega

private theorem incL_tail_2m_defined (k : Nat) (u : RegState) (m : Nat)
    (hm : u rM = m) (hm2 : 2 ≤ m) (hmM : m < M) (h2m : 2 * m < M) :
    SAllDefined k u (lPre2M ++ lDiv2M :: (lPreM1 ++ [lDivM1])) := by
  refine sAllDefined_stage (by rfl) (sDefined_udiv ?_) ?_
  · rw [denoteOperand_reg, two_m_srun k u m hm h2m]
    omega
  apply incL_tail_m1_defined k _ m
  · rw [srun_frame k rM _ (by rfl), hm]
  · exact hm2
  · exact hmM

theorem incLBlock_defined (k : Nat) (u : RegState) (m : Nat)
    (hm : u rM = m) (hm2 : 2 ≤ m) (hmM : m < M) (h2m : 2 * m < M) :
    SAllDefined k u incLBlock := by
  rw [incLBlock_split]
  refine sAllDefined_stage (by rfl) (sDefined_udiv ?_) ?_
  · rw [denoteOperand_reg, srun_frame k rM _ (by rfl), hm]
    omega
  apply incL_tail_2m_defined k _ m
  · rw [srun_frame k rM _ (by rfl), hm]
  · exact hm2
  · exact hmM
  · exact h2m

private theorem incU_tail_m1_defined (k : Nat) (u : RegState) (m : Nat)
    (hm : u rM = m) (hm2 : 2 ≤ m) (hmM : m < M) :
    SAllDefined k u (uPreM1 ++ [uDivM1]) := by
  refine sAllDefined_stage (by rfl) (sDefined_udiv ?_)
    (sAllDefined_of_noDiv k _ _ (by rfl))
  rw [denoteOperand_reg, m_sub_one_srun_u k u m hm hm2 hmM]
  omega

private theorem incU_tail_2m_defined (k : Nat) (u : RegState) (m : Nat)
    (hm : u rM = m) (hm2 : 2 ≤ m) (hmM : m < M) (h2m : 2 * m < M) :
    SAllDefined k u (uPre2M ++ uDiv2M :: (uPreM1 ++ [uDivM1])) := by
  refine sAllDefined_stage (by rfl) (sDefined_udiv ?_) ?_
  · rw [denoteOperand_reg, two_m_srun_u k u m hm h2m]
    omega
  apply incU_tail_m1_defined k _ m
  · rw [srun_frame k rM _ (by rfl), hm]
  · exact hm2
  · exact hmM

theorem incUBlock_defined (k : Nat) (u : RegState) (m : Nat)
    (hm : u rM = m) (hm2 : 2 ≤ m) (hmM : m < M) (h2m : 2 * m < M) :
    SAllDefined k u incUBlock := by
  rw [incUBlock_split]
  refine sAllDefined_stage (by rfl) (sDefined_udiv ?_) ?_
  · rw [denoteOperand_reg, srun_frame k rM _ (by rfl), hm]
    omega
  apply incU_tail_2m_defined k _ m
  · rw [srun_frame k rM _ (by rfl), hm]
  · exact hm2
  · exact hmM
  · exact h2m

private def commitPre (B : Nat) : List Instr :=
  [ .binop rC .eq (.reg rR) (.lit (B - 1))
  , .binop rT1 .eq (.reg rAcc) (.lit 0)
  , .binop rPr .mul (.reg rC) (.reg rT1)
  , .binop rM .sub (.reg rN) (.lit 1) ]

private def commitPost : List Instr :=
  [ .binop rT1 .mul (.reg rPr) (.reg rIL)
  , .binop rSL .add (.reg rSL) (.reg rT1)
  , .binop rT2 .mul (.reg rPr) (.reg rIU)
  , .binop rSU .add (.reg rSU) (.reg rT2)
  , .binop rT1 .sub (.lit 1) (.reg rC)
  , .binop rAcc .mul (.reg rT1) (.reg rAcc) ]

private theorem commitBlock_split (B : Nat) :
    commitBlock B = ((commitPre B ++ incLBlock) ++ incUBlock) ++ commitPost :=
  rfl

private theorem commitPre_rM (B k : Nat) (u : RegState) (n : Nat)
    (hn : u rN = n) (hn1 : 1 ≤ n) (hnM : n < M) :
    srun k u (commitPre B) rM = n - 1 := by
  rw [show commitPre B =
      [ .binop rC .eq (.reg rR) (.lit (B - 1))
      , .binop rT1 .eq (.reg rAcc) (.lit 0)
      , .binop rPr .mul (.reg rC) (.reg rT1) ] ++
        [ .binop rM .sub (.reg rN) (.lit 1) ] from rfl,
    srun_read_last k rM _ _ rfl]
  apply sval_binop_val
  · rw [denoteOperand_reg, srun_frame k rN _ (by rfl), hn]
  · exact denoteOperand_lit_of_lt k _ (by decide)
  · exact denoteOp_sub_of_le hn1 hnM

/-- All seven divisions in the fixed 32-instruction commit block are defined
whenever its decoded candidate is in the production word-safe range.  This is
a block-sized symbolic proof; it does not run a candidate loop. -/
theorem commitBlock_defined (B k : Nat) (u : RegState) (n : Nat)
    (hn : u rN = n) (hn3 : 3 ≤ n) (hn40 : n ≤ 2 ^ 40) :
    SAllDefined k u (commitBlock B) := by
  have hnM : n < M := Nat.lt_of_le_of_lt hn40 (by decide)
  let m := n - 1
  have hm2 : 2 ≤ m := by dsimp [m]; omega
  have hmM : m < M := Nat.lt_of_le_of_lt (Nat.sub_le n 1) hnM
  have h2m : 2 * m < M := by
    dsimp [m]
    exact Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_left 2 (Nat.le_trans (Nat.sub_le n 1) hn40))
      (by decide)
  rw [commitBlock_split]
  apply sAllDefined_append
  · apply sAllDefined_append
    · exact sAllDefined_append
        (sAllDefined_of_noDiv k (commitPre B) u (by rfl))
        (incLBlock_defined k _ m
          (commitPre_rM B k u n hn (by omega) hnM) hm2 hmM h2m)
    · apply incUBlock_defined k _ m
      · rw [srun_append, srun_frame k rM incLBlock (by rfl)]
        exact commitPre_rM B k u n hn (by omega) hnM
      · exact hm2
      · exact hmM
      · exact h2m
  · exact sAllDefined_of_noDiv k commitPost _ (by rfl)

/-- The partial instruction semantics of the commit block reaches its total
straight-line model.  The theorem is independent of the production range
length and is the entry point for the register-value refinement lemmas. -/
theorem commitBlock_denote (B k : Nat) (u : RegState) (n : Nat)
    (hn : u rN = n) (hn3 : 3 ≤ n) (hn40 : n ≤ 2 ^ 40) :
    denoteInstrs k u (commitBlock B) = some (srun k u (commitBlock B)) :=
  denoteInstrs_eq_srun k _ _ (commitBlock_defined B k u n hn hn3 hn40)

/-! ## Exact increment values

The following walks name one instruction at a time.  This is intentionally
more explicit than a broad `simp [srun]`: the latter expands a tower of
register updates and was the source of the old high-memory proof path.
-/

private def l0 : Instr := .binop rT1 .mul (.reg rM) (.lit 2)
private def l1 : Instr := .binop rT1 .add (.reg rT1) (.lit (3 * fpD))
private def l3 : Instr := .binop rT1 .add (.reg rT1) (.reg rT2)
private def l4 : Instr := .binop rT2 .mul (.reg rM) (.lit 2)
private def l6 : Instr := .binop rT1 .sub (.lit fpD) (.reg rT1)
private def l7 : Instr := .binop rT2 .sub (.reg rM) (.lit 1)

private def lp1 : List Instr := [l0]
private def lp2 : List Instr := lp1 ++ [l1]
private def lp3 : List Instr := lp2 ++ [lDivM]
private def lp4 : List Instr := lp3 ++ [l3]
private def lp5 : List Instr := lp4 ++ [l4]
private def lp6 : List Instr := lp5 ++ [lDiv2M]
private def lp7 : List Instr := lp6 ++ [l6]
private def lp8 : List Instr := lp7 ++ [l7]
private def lp9 : List Instr := lp8 ++ [lDivM1]

private theorem incLBlock_eq_lp9 : incLBlock = lp9 := rfl

private theorem incL_correction_le (m : Nat) (hm2 : 2 ≤ m) :
    ((3 * fpD + 2 * m) + (fpD - 1) / m) / (2 * m) ≤ fpD := by
  have hdiv : (fpD - 1) / m ≤ fpD - 1 := Nat.div_le_self _ _
  have hscale : 4 * fpD ≤ 2 * m * fpD := by
    have h := Nat.mul_le_mul_left (2 * fpD) hm2
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hnum : (3 * fpD + 2 * m) + (fpD - 1) / m <
      (fpD + 1) * (2 * m) := by
    have hdivlt : (fpD - 1) / m < fpD := by
      exact Nat.lt_of_le_of_lt hdiv (by
        have := fpD_pos
        omega)
    calc
      (3 * fpD + 2 * m) + (fpD - 1) / m
          < 4 * fpD + 2 * m := by omega
      _ ≤ 2 * m * fpD + 2 * m := Nat.add_le_add_right hscale _
      _ = (fpD + 1) * (2 * m) := by
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
  have hpos : 0 < 2 * m := by omega
  have hq : ((3 * fpD + 2 * m) + (fpD - 1) / m) / (2 * m) < fpD + 1 :=
    (Nat.div_lt_iff_lt_mul hpos).2 hnum
  omega

/-- The nine-instruction lower-increment block computes `incLWord` exactly;
all hypotheses are scalar word-range facts, independent of any loop count. -/
theorem incLBlock_rIL (k : Nat) (u : RegState) (m : Nat)
    (hm : u rM = m) (hm2 : 2 ≤ m) (hm40 : m ≤ 2 ^ 40) :
    srun k u incLBlock rIL = incLWord m := by
  have hmM : m < M := Nat.lt_of_le_of_lt hm40 (by decide)
  have h2m : 2 * m < M :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hm40) (by decide)
  have hwide := incLWord_intermediate_lt m hm2 hm40
  have hwideM : (3 * fpD + 2 * m) + (fpD - 1) / m < M :=
    Nat.lt_trans hwide (by decide)
  have hm0 : m ≠ 0 := by omega
  have h2m0 : 2 * m ≠ 0 := by omega
  have hm10 : m - 1 ≠ 0 := by omega
  have e0 : srun k u lp1 rT1 = 2 * m := by
    apply step_write (q := lp1) (p := []) (op := .mul)
      (l := .reg rM) (r := .lit 2) (a := m) (b := 2) (v := 2 * m) (by rfl)
    · rw [denoteOperand_reg]
      exact hm
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · simpa [Nat.mul_comm] using
        (denoteOp_mul_of_lt (show m * 2 < M by omega))
  have e1 : srun k u lp2 rT1 = 3 * fpD + 2 * m := by
    apply step_write (q := lp2) (p := lp1) (by rfl)
    · rw [denoteOperand_reg, e0]
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · simpa [Nat.add_comm] using
        (denoteOp_add_of_lt
          (show 2 * m + 3 * fpD < M by
            calc
              2 * m + 3 * fpD = 3 * fpD + 2 * m := Nat.add_comm _ _
              _ ≤ (3 * fpD + 2 * m) + (fpD - 1) / m :=
                Nat.le_add_right _ _
              _ < M := hwideM))
  have e2 : srun k u lp3 rT2 = (fpD - 1) / m := by
    apply step_write (q := lp3) (p := lp2) (by rfl)
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · rw [denoteOperand_reg, srun_frame k rM lp2 (by rfl), hm]
    · exact denoteOp_udiv_of_ne hm0 (by decide)
  have e3 : srun k u lp4 rT1 =
      (3 * fpD + 2 * m) + (fpD - 1) / m := by
    apply step_write (q := lp4) (p := lp3) (by rfl)
    · rw [denoteOperand_reg,
        show lp3 = lp2 ++ [lDivM] from rfl,
        srun_frame_append k rT1 lp2 [lDivM] (by rfl), e1]
    · rw [denoteOperand_reg, e2]
    · exact denoteOp_add_of_lt hwideM
  have e4 : srun k u lp5 rT2 = 2 * m := by
    apply step_write (q := lp5) (p := lp4) (by rfl)
    · rw [denoteOperand_reg, srun_frame k rM lp4 (by rfl), hm]
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · simpa [Nat.mul_comm] using
        (denoteOp_mul_of_lt (show m * 2 < M by omega))
  have e5 : srun k u lp6 rT1 =
      ((3 * fpD + 2 * m) + (fpD - 1) / m) / (2 * m) := by
    apply step_write (q := lp6) (p := lp5) (by rfl)
    · rw [denoteOperand_reg,
        show lp5 = lp4 ++ [l4] from rfl,
        srun_frame_append k rT1 lp4 [l4] (by rfl), e3]
    · rw [denoteOperand_reg, e4]
    · exact denoteOp_udiv_of_ne h2m0 hwideM
  have hcorr := incL_correction_le m hm2
  have e6 : srun k u lp7 rT1 =
      fpD - ((3 * fpD + 2 * m) + (fpD - 1) / m) / (2 * m) := by
    apply step_write (q := lp7) (p := lp6) (by rfl)
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · rw [denoteOperand_reg, e5]
    · exact denoteOp_sub_of_le hcorr (by decide)
  have e7 : srun k u lp8 rT2 = m - 1 := by
    apply step_write (q := lp8) (p := lp7) (by rfl)
    · rw [denoteOperand_reg, srun_frame k rM lp7 (by rfl), hm]
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · exact denoteOp_sub_of_le (by omega) hmM
  rw [incLBlock_eq_lp9]
  apply Eq.trans (step_write (q := lp9) (p := lp8) (by rfl)
    (by
      rw [denoteOperand_reg,
        show lp8 = lp7 ++ [l7] from rfl,
        srun_frame_append k rT1 lp7 [l7] (by rfl), e6])
    (by rw [denoteOperand_reg, e7])
    (denoteOp_udiv_of_ne hm10
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide))))
  rfl

private def u0 : Instr := .binop rT1 .mul (.reg rM) (.lit 2)
private def u1 : Instr := .binop rT1 .add (.reg rT1) (.lit (3 * fpD))
private def u2 : Instr := .binop rT2 .add (.reg rM) (.lit (3 * fpD))
private def u3 : Instr := .binop rT2 .sub (.reg rT2) (.lit 1)
private def u5 : Instr := .binop rT1 .sub (.reg rT1) (.reg rT2)
private def u6 : Instr := .binop rT2 .mul (.reg rM) (.lit 2)
private def u8 : Instr := .binop rT2 .add (.reg rM) (.lit fpD)
private def u9 : Instr := .binop rT2 .sub (.reg rT2) (.lit 1)
private def u10 : Instr := .binop rT1 .sub (.reg rT2) (.reg rT1)
private def u11 : Instr := .binop rT2 .sub (.reg rM) (.lit 1)

private def up1 : List Instr := [u0]
private def up2 : List Instr := up1 ++ [u1]
private def up3 : List Instr := up2 ++ [u2]
private def up4 : List Instr := up3 ++ [u3]
private def up5 : List Instr := up4 ++ [uDivM]
private def up6 : List Instr := up5 ++ [u5]
private def up7 : List Instr := up6 ++ [u6]
private def up8 : List Instr := up7 ++ [uDiv2M]
private def up9 : List Instr := up8 ++ [u8]
private def up10 : List Instr := up9 ++ [u9]
private def up11 : List Instr := up10 ++ [u10]
private def up12 : List Instr := up11 ++ [u11]
private def up13 : List Instr := up12 ++ [uDivM1]

private theorem incUBlock_eq_up13 : incUBlock = up13 := rfl

private theorem div_anti_den {a p q : Nat} (hpq : p ≤ q) (hp : 0 < p) :
    a / q ≤ a / p := by
  rw [Nat.le_div_iff_mul_le hp]
  exact Nat.le_trans (Nat.mul_le_mul_left _ hpq) (Nat.div_mul_le_self a q)

private theorem incU_correction_le (m : Nat) (hm2 : 2 ≤ m) :
    ((3 * fpD + 2 * m) - (3 * fpD + m - 1) / m) / (2 * m) ≤
      fpD + m - 1 := by
  have hpos : 0 < 2 * m := by omega
  have s1 : ((3 * fpD + 2 * m) - (3 * fpD + m - 1) / m) / (2 * m)
      ≤ (3 * fpD + 2 * m) / (2 * m) :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have s2 : (3 * fpD + 2 * m) / (2 * m) = 3 * fpD / (2 * m) + 1 :=
    Nat.add_div_right _ hpos
  have s3 : 3 * fpD / (2 * m) ≤ 3 * fpD / 4 :=
    div_anti_den (by omega) (by decide)
  have s4 : 3 * fpD / 4 + 1 ≤ fpD - 1 := by decide
  have hD : 1 ≤ fpD := by decide
  omega

/-- The thirteen-instruction upper-increment block computes `incUWord`
exactly, without evaluating any enclosing fold. -/
theorem incUBlock_rIU (k : Nat) (u : RegState) (m : Nat)
    (hm : u rM = m) (hm2 : 2 ≤ m) (hm40 : m ≤ 2 ^ 40) :
    srun k u incUBlock rIU = incUWord m := by
  have hmM : m < M := Nat.lt_of_le_of_lt hm40 (by decide)
  have h2m : 2 * m < M :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hm40) (by decide)
  have h3m : 3 * fpD + m < M :=
    Nat.lt_trans (incUWord_intermediate_lt m hm2 hm40) (by decide)
  have h32m : 3 * fpD + 2 * m < M := by
    have hD : fpD = 2 ^ 48 := by decide
    rw [hD]
    exact Nat.lt_of_le_of_lt
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hm40) (3 * 2 ^ 48))
      (by decide)
  have hDm : fpD + m < M := by
    have hD : fpD = 2 ^ 48 := by decide
    omega
  have hm0 : m ≠ 0 := by omega
  have h2m0 : 2 * m ≠ 0 := by omega
  have hm10 : m - 1 ≠ 0 := by omega
  have e0 : srun k u up1 rT1 = 2 * m := by
    apply step_write (q := up1) (p := []) (op := .mul)
      (l := .reg rM) (r := .lit 2) (a := m) (b := 2) (v := 2 * m) (by rfl)
    · rw [denoteOperand_reg]
      exact hm
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · simpa [Nat.mul_comm] using
        (denoteOp_mul_of_lt (show m * 2 < M by omega))
  have e1 : srun k u up2 rT1 = 3 * fpD + 2 * m := by
    apply step_write (q := up2) (p := up1) (by rfl)
    · rw [denoteOperand_reg, e0]
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · simpa [Nat.add_comm] using
        (denoteOp_add_of_lt (show 2 * m + 3 * fpD < M by omega))
  have e2 : srun k u up3 rT2 = 3 * fpD + m := by
    apply step_write (q := up3) (p := up2) (by rfl)
    · rw [denoteOperand_reg, srun_frame k rM up2 (by rfl), hm]
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · simpa [Nat.add_comm] using
        (denoteOp_add_of_lt (show m + 3 * fpD < M by omega))
  have e3 : srun k u up4 rT2 = 3 * fpD + m - 1 := by
    apply step_write (q := up4) (p := up3) (by rfl)
    · rw [denoteOperand_reg, e2]
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · exact denoteOp_sub_of_le (by have := fpD_pos; omega) h3m
  have e4 : srun k u up5 rT2 = (3 * fpD + m - 1) / m := by
    apply step_write (q := up5) (p := up4) (by rfl)
    · rw [denoteOperand_reg, e3]
    · rw [denoteOperand_reg, srun_frame k rM up4 (by rfl), hm]
    · exact denoteOp_udiv_of_ne hm0
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h3m)
  have e5 : srun k u up6 rT1 =
      (3 * fpD + 2 * m) - (3 * fpD + m - 1) / m := by
    apply step_write (q := up6) (p := up5) (by rfl)
    · rw [denoteOperand_reg,
        show up5 = up4 ++ [uDivM] from rfl,
        srun_frame_append k rT1 up4 [uDivM] (by rfl),
        show up4 = up3 ++ [u3] from rfl,
        srun_frame_append k rT1 up3 [u3] (by rfl),
        show up3 = up2 ++ [u2] from rfl,
        srun_frame_append k rT1 up2 [u2] (by rfl), e1]
    · rw [denoteOperand_reg, e4]
    · exact denoteOp_sub_of_le
        (Nat.le_trans (Nat.div_le_self _ _) (by omega)) h32m
  have e6 : srun k u up7 rT2 = 2 * m := by
    apply step_write (q := up7) (p := up6) (by rfl)
    · rw [denoteOperand_reg, srun_frame k rM up6 (by rfl), hm]
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · simpa [Nat.mul_comm] using
        (denoteOp_mul_of_lt (show m * 2 < M by omega))
  have e7 : srun k u up8 rT1 =
      ((3 * fpD + 2 * m) - (3 * fpD + m - 1) / m) / (2 * m) := by
    apply step_write (q := up8) (p := up7) (by rfl)
    · rw [denoteOperand_reg,
        show up7 = up6 ++ [u6] from rfl,
        srun_frame_append k rT1 up6 [u6] (by rfl), e5]
    · rw [denoteOperand_reg, e6]
    · exact denoteOp_udiv_of_ne h2m0
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h32m)
  have e8 : srun k u up9 rT2 = fpD + m := by
    apply step_write (q := up9) (p := up8) (by rfl)
    · rw [denoteOperand_reg, srun_frame k rM up8 (by rfl), hm]
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · simpa [Nat.add_comm] using
        (denoteOp_add_of_lt (show m + fpD < M by omega))
  have e9 : srun k u up10 rT2 = fpD + m - 1 := by
    apply step_write (q := up10) (p := up9) (by rfl)
    · rw [denoteOperand_reg, e8]
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · exact denoteOp_sub_of_le (by have := fpD_pos; omega) hDm
  have hcorr := incU_correction_le m hm2
  have e10 : srun k u up11 rT1 =
      (fpD + m - 1) -
        ((3 * fpD + 2 * m) - (3 * fpD + m - 1) / m) / (2 * m) := by
    apply step_write (q := up11) (p := up10) (by rfl)
    · rw [denoteOperand_reg, e9]
    · rw [denoteOperand_reg,
        show up10 = up9 ++ [u9] from rfl,
        srun_frame_append k rT1 up9 [u9] (by rfl),
        show up9 = up8 ++ [u8] from rfl,
        srun_frame_append k rT1 up8 [u8] (by rfl), e7]
    · exact denoteOp_sub_of_le hcorr
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hDm)
  have e11 : srun k u up12 rT2 = m - 1 := by
    apply step_write (q := up12) (p := up11) (by rfl)
    · rw [denoteOperand_reg, srun_frame k rM up11 (by rfl), hm]
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · exact denoteOp_sub_of_le (by omega) hmM
  rw [incUBlock_eq_up13]
  apply Eq.trans (step_write (q := up13) (p := up12)
    (a := (fpD + m - 1) -
      ((3 * fpD + 2 * m) - (3 * fpD + m - 1) / m) / (2 * m))
    (b := m - 1)
    (v := ((fpD + m - 1) -
      ((3 * fpD + 2 * m) - (3 * fpD + m - 1) / m) / (2 * m)) / (m - 1))
    (by rfl)
    (by
      rw [denoteOperand_reg,
        show up12 = up11 ++ [u11] from rfl,
        srun_frame_append k rT1 up11 [u11] (by rfl), e10])
    (by rw [denoteOperand_reg, e11])
    (denoteOp_udiv_of_ne hm10
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hDm))))
  rfl

/-! ## The prime gate and commit observation -/

private def c0 (B : Nat) : Instr :=
  .binop rC .eq (.reg rR) (.lit (B - 1))
private def c1 : Instr :=
  .binop rT1 .eq (.reg rAcc) (.lit 0)
private def c2 : Instr :=
  .binop rPr .mul (.reg rC) (.reg rT1)
private def c3 : Instr :=
  .binop rM .sub (.reg rN) (.lit 1)

private def cp1 (B : Nat) : List Instr := [c0 B]
private def cp2 (B : Nat) : List Instr := cp1 B ++ [c1]
private def cp3 (B : Nat) : List Instr := cp2 B ++ [c2]
private def cp4 (B : Nat) : List Instr := cp3 B ++ [c3]

private theorem commitPre_eq_cp4 (B : Nat) : commitPre B = cp4 B := rfl

private theorem commitPre_rC (B k : Nat) (u : RegState) (hBM : B - 1 < M) :
    srun k u (commitPre B) rC = if u rR = B - 1 then 1 else 0 := by
  rw [commitPre_eq_cp4,
    show cp4 B = cp1 B ++ [c1, c2, c3] from rfl,
    srun_frame_append k rC (cp1 B) [c1, c2, c3] (by rfl),
    show cp1 B = [] ++ [c0 B] from rfl,
    srun_read_last k rC [] (c0 B) rfl]
  apply sval_binop_val
  · rw [denoteOperand_reg]
  · exact denoteOperand_lit_of_lt k _ hBM
  · exact denoteOp_eq_val _ _

private theorem commitPre_rT1_gate (B k : Nat) (u : RegState) :
    srun k u (cp2 B) rT1 = if u rAcc = 0 then 1 else 0 := by
  apply step_write (q := cp2 B) (p := cp1 B) (by rfl)
  · rw [denoteOperand_reg, srun_frame k rAcc (cp1 B) (by rfl)]
  · exact denoteOperand_lit_of_lt k _ (by decide)
  · exact denoteOp_eq_val _ _

private theorem commitPre_rPr (B k : Nat) (u : RegState) (hBM : B - 1 < M) :
    srun k u (commitPre B) rPr =
      if u rR = B - 1 ∧ u rAcc = 0 then 1 else 0 := by
  have hc : srun k u (cp2 B) rC = if u rR = B - 1 then 1 else 0 := by
    rw [show cp2 B = cp1 B ++ [c1] from rfl,
      srun_frame_append k rC (cp1 B) [c1] (by rfl),
      show cp1 B = [] ++ [c0 B] from rfl,
      srun_read_last k rC [] (c0 B) rfl]
    apply sval_binop_val
    · rw [denoteOperand_reg]
    · exact denoteOperand_lit_of_lt k _ hBM
    · exact denoteOp_eq_val _ _
  have ht := commitPre_rT1_gate B k u
  have hp : srun k u (cp3 B) rPr =
      if u rR = B - 1 ∧ u rAcc = 0 then 1 else 0 := by
    apply step_write (q := cp3 B) (p := cp2 B) (by rfl)
    · rw [denoteOperand_reg, hc]
    · rw [denoteOperand_reg, ht]
    · by_cases hr : u rR = B - 1 <;> by_cases ha : u rAcc = 0 <;>
        simp [hr, ha, denoteOp, Nat.mod_eq_of_lt (by decide : 1 < M)]
  rw [commitPre_eq_cp4,
    show cp4 B = cp3 B ++ [c3] from rfl,
    srun_frame_append k rPr (cp3 B) [c3] (by rfl), hp]

private def p0 : Instr := .binop rT1 .mul (.reg rPr) (.reg rIL)
private def p1 : Instr := .binop rSL .add (.reg rSL) (.reg rT1)
private def p2 : Instr := .binop rT2 .mul (.reg rPr) (.reg rIU)
private def p3 : Instr := .binop rSU .add (.reg rSU) (.reg rT2)
private def p4 : Instr := .binop rT1 .sub (.lit 1) (.reg rC)
private def p5 : Instr := .binop rAcc .mul (.reg rT1) (.reg rAcc)

private def pp1 : List Instr := [p0]
private def pp2 : List Instr := pp1 ++ [p1]
private def pp3 : List Instr := pp2 ++ [p2]
private def pp4 : List Instr := pp3 ++ [p3]
private def pp5 : List Instr := pp4 ++ [p4]
private def pp6 : List Instr := pp5 ++ [p5]

private theorem commitPost_eq_pp6 : commitPost = pp6 := rfl

private theorem commitPost_vals (k : Nat) (x : RegState)
    (C P : Prop) [Decidable C] [Decidable P] (il iu : Nat)
    (hC : x rC = if C then 1 else 0)
    (hP : x rPr = if P then 1 else 0)
    (hIL : x rIL = il) (hIU : x rIU = iu)
    (hSLM : x rSL < M) (hSUM : x rSU < M) (hAccM : x rAcc < M)
    (hilM : il < M) (hiuM : iu < M)
    (hSLadd : x rSL + il < M) (hSUadd : x rSU + iu < M) :
    srun k x commitPost rSL = x rSL + (if P then il else 0) ∧
    srun k x commitPost rSU = x rSU + (if P then iu else 0) ∧
    srun k x commitPost rAcc = if C then 0 else x rAcc := by
  have e0 : srun k x pp1 rT1 = if P then il else 0 := by
    apply step_write (q := pp1) (p := []) (op := .mul)
      (l := .reg rPr) (r := .reg rIL)
      (a := if P then 1 else 0) (b := il) (v := if P then il else 0) (by rfl)
    · rw [denoteOperand_reg]
      exact hP
    · rw [denoteOperand_reg]
      exact hIL
    · by_cases hp : P <;> simp [hp, denoteOp, Nat.mod_eq_of_lt hilM]
  have e1 : srun k x pp2 rSL = x rSL + (if P then il else 0) := by
    apply step_write (q := pp2) (p := pp1) (by rfl)
    · rw [denoteOperand_reg, srun_frame k rSL pp1 (by rfl)]
    · rw [denoteOperand_reg, e0]
    · apply denoteOp_add_of_lt
      by_cases hp : P
      · simpa [hp] using hSLadd
      · simpa [hp] using hSLM
  have e2 : srun k x pp3 rT2 = if P then iu else 0 := by
    apply step_write (q := pp3) (p := pp2) (by rfl)
    · rw [denoteOperand_reg, srun_frame k rPr pp2 (by rfl), hP]
    · rw [denoteOperand_reg, srun_frame k rIU pp2 (by rfl), hIU]
    · by_cases hp : P <;> simp [hp, denoteOp, Nat.mod_eq_of_lt hiuM]
  have e3 : srun k x pp4 rSU = x rSU + (if P then iu else 0) := by
    apply step_write (q := pp4) (p := pp3) (by rfl)
    · rw [denoteOperand_reg, srun_frame k rSU pp3 (by rfl)]
    · rw [denoteOperand_reg, e2]
    · apply denoteOp_add_of_lt
      by_cases hp : P
      · simpa [hp] using hSUadd
      · simpa [hp] using hSUM
  have e4 : srun k x pp5 rT1 = if C then 0 else 1 := by
    apply step_write (q := pp5) (p := pp4) (by rfl)
    · exact denoteOperand_lit_of_lt k _ (by decide)
    · rw [denoteOperand_reg, srun_frame k rC pp4 (by rfl), hC]
    · by_cases hc : C
      · simpa [hc] using
          (denoteOp_sub_of_le (a := 1) (b := 1) (by decide) (by decide))
      · simpa [hc] using
          (denoteOp_sub_of_le (a := 1) (b := 0) (by decide) (by decide))
  have e5 : srun k x pp6 rAcc = if C then 0 else x rAcc := by
    apply step_write (q := pp6) (p := pp5) (by rfl)
    · rw [denoteOperand_reg, e4]
    · rw [denoteOperand_reg, srun_frame k rAcc pp5 (by rfl)]
    · by_cases hc : C <;> simp [hc, denoteOp, Nat.mod_eq_of_lt hAccM]
  rw [commitPost_eq_pp6]
  exact ⟨
    (srun_frame_append k rSL pp2 [p2, p3, p4, p5] (by rfl) x).trans e1,
    (srun_frame_append k rSU pp4 [p4, p5] (by rfl) x).trans e3,
    e5⟩

/-- The complete commit observation.  On the final round, a candidate whose
scan accumulator is zero contributes the exact word-safe increments; every
final round clears the scan accumulator.  The additions are stated under the
same explicit no-wrap premises required by the source ladder invariant. -/
theorem commitBlock_vals (B k : Nat) (u : RegState) (n : Nat)
    (hn : u rN = n) (hn3 : 3 ≤ n) (hn40 : n ≤ 2 ^ 40)
    (hBM : B - 1 < M)
    (hSLM : u rSL < M) (hSUM : u rSU < M) (hAccM : u rAcc < M)
    (hSLadd : u rSL + incLWord (n - 1) < M)
    (hSUadd : u rSU + incUWord (n - 1) < M) :
    srun k u (commitBlock B) rSL =
      u rSL + (if u rR = B - 1 ∧ u rAcc = 0 then incLWord (n - 1) else 0) ∧
    srun k u (commitBlock B) rSU =
      u rSU + (if u rR = B - 1 ∧ u rAcc = 0 then incUWord (n - 1) else 0) ∧
    srun k u (commitBlock B) rAcc =
      if u rR = B - 1 then 0 else u rAcc := by
  let m := n - 1
  have hm2 : 2 ≤ m := by dsimp [m]; omega
  have hm40 : m ≤ 2 ^ 40 := Nat.le_trans (Nat.sub_le n 1) hn40
  have hnM : n < M := Nat.lt_of_le_of_lt hn40 (by decide)
  let v := srun k u (commitPre B)
  let w := srun k v incLBlock
  let x := srun k w incUBlock
  have hvm : v rM = m := by
    dsimp [v, m]
    exact commitPre_rM B k u n hn (by omega) hnM
  have hwm : w rM = m := by
    dsimp [w]
    rw [srun_frame k rM incLBlock (by rfl), hvm]
  have hxm : x rM = m := by
    dsimp [x]
    rw [srun_frame k rM incUBlock (by rfl), hwm]
  have hILw : w rIL = incLWord m := by
    dsimp [w]
    exact incLBlock_rIL k v m hvm hm2 hm40
  have hILx : x rIL = incLWord m := by
    dsimp [x]
    rw [srun_frame k rIL incUBlock (by rfl), hILw]
  have hIUx : x rIU = incUWord m := by
    dsimp [x]
    exact incUBlock_rIU k w m hwm hm2 hm40
  have hCv : v rC = if u rR = B - 1 then 1 else 0 := by
    dsimp [v]
    exact commitPre_rC B k u hBM
  have hCx : x rC = if u rR = B - 1 then 1 else 0 := by
    calc
      x rC = w rC := by dsimp [x]; exact srun_frame k rC incUBlock (by rfl) w
      _ = v rC := by dsimp [w]; exact srun_frame k rC incLBlock (by rfl) v
      _ = _ := hCv
  have hPrv : v rPr =
      if u rR = B - 1 ∧ u rAcc = 0 then 1 else 0 := by
    dsimp [v]
    exact commitPre_rPr B k u hBM
  have hPrx : x rPr =
      if u rR = B - 1 ∧ u rAcc = 0 then 1 else 0 := by
    calc
      x rPr = w rPr := by dsimp [x]; exact srun_frame k rPr incUBlock (by rfl) w
      _ = v rPr := by dsimp [w]; exact srun_frame k rPr incLBlock (by rfl) v
      _ = _ := hPrv
  have hSLv : v rSL = u rSL := by
    dsimp [v]; exact srun_frame k rSL (commitPre B) (by rfl) u
  have hSLx : x rSL = u rSL := by
    calc
      x rSL = w rSL := by dsimp [x]; exact srun_frame k rSL incUBlock (by rfl) w
      _ = v rSL := by dsimp [w]; exact srun_frame k rSL incLBlock (by rfl) v
      _ = _ := hSLv
  have hSUv : v rSU = u rSU := by
    dsimp [v]; exact srun_frame k rSU (commitPre B) (by rfl) u
  have hSUx : x rSU = u rSU := by
    calc
      x rSU = w rSU := by dsimp [x]; exact srun_frame k rSU incUBlock (by rfl) w
      _ = v rSU := by dsimp [w]; exact srun_frame k rSU incLBlock (by rfl) v
      _ = _ := hSUv
  have hAccv : v rAcc = u rAcc := by
    dsimp [v]; exact srun_frame k rAcc (commitPre B) (by rfl) u
  have hAccx : x rAcc = u rAcc := by
    calc
      x rAcc = w rAcc := by dsimp [x]; exact srun_frame k rAcc incUBlock (by rfl) w
      _ = v rAcc := by dsimp [w]; exact srun_frame k rAcc incLBlock (by rfl) v
      _ = _ := hAccv
  have hilM : incLWord m < M :=
    Nat.lt_of_le_of_lt (incLWord_le m) (by decide)
  have hiuM : incUWord m < M := by
    exact Nat.lt_of_le_of_lt (incUWord_le m)
      (Nat.lt_of_le_of_lt (Nat.add_le_add_left hm40 fpD) (by decide))
  have hp := commitPost_vals k x
    (u rR = B - 1) (u rR = B - 1 ∧ u rAcc = 0)
    (incLWord m) (incUWord m) hCx hPrx hILx hIUx
    (by rw [hSLx]; exact hSLM) (by rw [hSUx]; exact hSUM)
    (by rw [hAccx]; exact hAccM) hilM hiuM
    (by simpa [m, hSLx] using hSLadd)
    (by simpa [m, hSUx] using hSUadd)
  have hshape : srun k u (commitBlock B) = srun k x commitPost := by
    rw [commitBlock_split, srun_append, srun_append, srun_append]
  rw [hshape]
  simpa [m, hSLx, hSUx, hAccx] using hp

/-- Partial denotation plus the mathematical observation, in the form used by
the surrounding body simulation. -/
theorem commitBlock_denote_vals (B k : Nat) (u : RegState) (n : Nat)
    (hn : u rN = n) (hn3 : 3 ≤ n) (hn40 : n ≤ 2 ^ 40)
    (hBM : B - 1 < M)
    (hSLM : u rSL < M) (hSUM : u rSU < M) (hAccM : u rAcc < M)
    (hSLadd : u rSL + incLWord (n - 1) < M)
    (hSUadd : u rSU + incUWord (n - 1) < M) :
    ∃ u', denoteInstrs k u (commitBlock B) = some u' ∧
      u' rSL = u rSL +
        (if u rR = B - 1 ∧ u rAcc = 0 then incLWord (n - 1) else 0) ∧
      u' rSU = u rSU +
        (if u rR = B - 1 ∧ u rAcc = 0 then incUWord (n - 1) else 0) ∧
      u' rAcc = if u rR = B - 1 then 0 else u rAcc := by
  refine ⟨srun k u (commitBlock B),
    commitBlock_denote B k u n hn hn3 hn40, ?_⟩
  exact commitBlock_vals B k u n hn hn3 hn40 hBM hSLM hSUM hAccM hSLadd hSUadd

/-! ## One complete flat round -/

/-- Mathematical accumulator transition of one trial-divisor round. -/
def scanNext (a n d : Nat) : Nat :=
  if a = 0 ∧ d * d ≤ n ∧ n % d = 0 then d else a

theorem scanNext_lt (a n d : Nat) (ha : a < M) (hd : d < M) :
    scanNext a n d < M := by
  unfold scanNext
  split
  · exact hd
  · exact ha

/-- Observable transition of one flattened `(candidate, divisor)` round. -/
def flatRound (n0 B i SL SU acc : Nat) : Nat × Nat × Nat :=
  let r := i % B
  let n := n0 + i / B
  let a' := scanNext acc n (r + 2)
  (SL + (if r = B - 1 ∧ a' = 0 then incLWord (n - 1) else 0),
   SU + (if r = B - 1 ∧ a' = 0 then incUWord (n - 1) else 0),
   if r = B - 1 then 0 else a')

theorem scanNext_eq_spfStep (a n r : Nat) :
    scanNext a n (r + 2) = Sieve.spfStep n a r := by
  rfl

/-- Decode, scan, and commit compose to `flatRound`.  All premises are scalar
range facts; the theorem's cost is independent of the loop count. -/
theorem ladderBody_denote_flatRound (n0 B i : Nat) (s : RegState)
    (hiM : i < M) (hBM : B < M) (hB0 : 0 < B)
    (hnM : n0 + i / B < M) (hdM : i % B + 2 < M)
    (hddM : (i % B + 2) * (i % B + 2) < M)
    (hn3 : 3 ≤ n0 + i / B) (hn40 : n0 + i / B ≤ 2 ^ 40)
    (hSLM : s rSL < M) (hSUM : s rSU < M) (hAccM : s rAcc < M)
    (hSLadd : s rSL + incLWord (n0 + i / B - 1) < M)
    (hSUadd : s rSU + incUWord (n0 + i / B - 1) < M) :
    ∃ s', denoteInstrs i s (ladderBody n0 B) = some s' ∧
      (s' rSL, s' rSU, s' rAcc) =
        flatRound n0 B i (s rSL) (s rSU) (s rAcc) := by
  let r := i % B
  let n := n0 + i / B
  let d := r + 2
  let a' := scanNext (s rAcc) n d
  let v := dstep n0 B i s
  have hBmod : B % M ≠ 0 := by
    rw [Nat.mod_eq_of_lt hBM]
    omega
  have hdecode : denoteInstrs i s (decodeBlock n0 B) = some v := by
    dsimp [v]
    exact decodeBlock_denote n0 B i s hBmod
  have hvals := dstep_vals n0 B i s hiM hBM hB0 hnM hdM
  change v rR = r ∧ v rN = n ∧ v rD = d ∧
    v rSL = s rSL ∧ v rSU = s rSU ∧ v rAcc = s rAcc at hvals
  obtain ⟨hvr, hvn, hvd, hvSL, hvSU, hvAcc⟩ := hvals
  let w := srun i v scanBlock
  have hscan : denoteInstrs i v scanBlock = some w := by
    dsimp [w]
    exact denoteInstrs_eq_srun i scanBlock v
      (scanBlock_defined i v (by rw [hvd]; dsimp [d, r]; omega))
  have hwa : w rAcc = a' := by
    dsimp [w, a']
    exact scanBlock_srun_rAcc i v (s rAcc) n d hvAcc hvn hvd
      hAccM hnM hdM hddM (by dsimp [d, r]; omega)
  have hwr : w rR = r := by
    dsimp [w]
    rw [srun_frame i rR scanBlock (by rfl), hvr]
  have hwn : w rN = n := by
    dsimp [w]
    rw [srun_frame i rN scanBlock (by rfl), hvn]
  have hwSL : w rSL = s rSL := by
    dsimp [w]
    rw [srun_frame i rSL scanBlock (by rfl), hvSL]
  have hwSU : w rSU = s rSU := by
    dsimp [w]
    rw [srun_frame i rSU scanBlock (by rfl), hvSU]
  have ha'M : a' < M := scanNext_lt (s rAcc) n d hAccM hdM
  have hwSLadd : w rSL + incLWord (n - 1) < M := by
    rw [hwSL]
    exact hSLadd
  have hwSUadd : w rSU + incUWord (n - 1) < M := by
    rw [hwSU]
    exact hSUadd
  obtain ⟨z, hz, hzvals⟩ := commitBlock_denote_vals B i w n hwn
    (by dsimp [n]; exact hn3) (by dsimp [n]; exact hn40)
    (Nat.lt_of_le_of_lt (Nat.sub_le B 1) hBM)
    (by rw [hwSL]; exact hSLM) (by rw [hwSU]; exact hSUM)
    (by rw [hwa]; exact ha'M)
    hwSLadd hwSUadd
  refine ⟨z, ?_, ?_⟩
  · change denoteInstrs i s
      (((decodeBlock n0 B ++ scanBlock) ++ commitBlock B)) = some z
    exact denoteInstrs_three_some i s v w z
      (decodeBlock n0 B) scanBlock (commitBlock B) hdecode hscan hz
  · change (z rSL, z rSU, z rAcc) =
      (s rSL + (if r = B - 1 ∧ a' = 0 then incLWord (n - 1) else 0),
       s rSU + (if r = B - 1 ∧ a' = 0 then incUWord (n - 1) else 0),
       if r = B - 1 then 0 else a')
    apply Prod.ext
    · simpa only [hwr, hwa, hwSL] using hzvals.1
    · apply Prod.ext
      · simpa only [hwr, hwa, hwSU] using hzvals.2.1
      · simpa only [hwr, hwa] using hzvals.2.2

/-! ## Reblocking one candidate -/

/-- `flatRound` as a fold step on the observable triple. -/
def flatObs (n0 B : Nat) (z : Nat × Nat × Nat) (i : Nat) :
    Nat × Nat × Nat :=
  flatRound n0 B i z.1 z.2.1 z.2.2

/-- The same round after its candidate and local divisor index are decoded. -/
def localRound (B n : Nat) (z : Nat × Nat × Nat) (r : Nat) :
    Nat × Nat × Nat :=
  let a' := scanNext z.2.2 n (r + 2)
  (z.1 + (if r = B - 1 ∧ a' = 0 then incLWord (n - 1) else 0),
   z.2.1 + (if r = B - 1 ∧ a' = 0 then incUWord (n - 1) else 0),
   if r = B - 1 then 0 else a')

theorem flatObs_shift (n0 B q r : Nat) (z : Nat × Nat × Nat)
    (hB : 0 < B) (hr : r < B) :
    flatObs n0 B z (q * B + r) = localRound B (n0 + q) z r := by
  have hmod : (q * B + r) % B = r := by
    rw [Nat.mul_comm q B, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hdiv : (q * B + r) / B = q := by
    rw [Nat.mul_comm q B, Nat.mul_add_div hB, Nat.div_eq_of_lt hr, Nat.add_zero]
  simp only [flatObs, flatRound, hmod, hdiv, localRound]

private theorem foldl_congr_mem {A : Type _} (l : List Nat)
    (f g : A → Nat → A)
    (h : ∀ a i, i ∈ l → f a i = g a i) :
    ∀ a, l.foldl f a = l.foldl g a := by
  induction l with
  | nil => intro a; rfl
  | cons i rest ih =>
      intro a
      rw [List.foldl_cons, List.foldl_cons, h a i (by simp)]
      apply ih
      intro a' j hj
      exact h a' j (by simp [hj])

/-- A prefix that has not reached the final round only advances `spfScan`;
the ladder accumulators are untouched. -/
theorem localRound_prefix (B n t SL SU : Nat) (ht : t < B) :
    (List.range t).foldl (localRound B n) (SL, SU, 0) =
      (SL, SU, Sieve.spfScan t n) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have ht' : t < B := by omega
      have hlast : t ≠ B - 1 := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih ht']
      simp only [localRound, hlast, false_and, if_false]
      rw [scanNext_eq_spfStep, ← Sieve.spfScan_succ]
      simp only [Nat.add_zero]

/-- Exactly `B` local rounds perform one candidate step, committing iff the
complete fixed-shape factor scan found no divisor. -/
theorem localRound_block (B n SL SU : Nat) (hB : 0 < B) :
    (List.range B).foldl (localRound B n) (SL, SU, 0) =
      (SL + (if Sieve.spfScan B n = 0 then incLWord (n - 1) else 0),
       SU + (if Sieve.spfScan B n = 0 then incUWord (n - 1) else 0), 0) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : B ≠ 0)
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    localRound_prefix (t + 1) n t SL SU (by omega)]
  simp only [localRound, Nat.add_one_sub_one]
  rw [scanNext_eq_spfStep, ← Sieve.spfScan_succ]
  by_cases h : Sieve.spfScan (t + 1) n = 0 <;> simp [h]

/-- The generic `BlockedFold.block` at candidate `q` is the local candidate
step above.  This is the flat-to-candidate reblocking needed by the program
denotation, and it performs no fold evaluation. -/
theorem flatObs_block (n0 B q SL SU : Nat) (hB : 0 < B) :
    BlockedFold.block B (flatObs n0 B) (SL, SU, 0) q =
      (SL + (if Sieve.spfScan B (n0 + q) = 0 then
          incLWord (n0 + q - 1) else 0),
       SU + (if Sieve.spfScan B (n0 + q) = 0 then
          incUWord (n0 + q - 1) else 0), 0) := by
  rw [BlockedFold.block_eq_shift]
  rw [foldl_congr_mem (List.range B)
    (fun z r => flatObs n0 B z (q * B + r))
    (localRound B (n0 + q))
    (fun z r hr => flatObs_shift n0 B q r z hB (List.mem_range.mp hr))]
  exact localRound_block B (n0 + q) SL SU hB

/-- Proof-oriented primality predicate used by the guarded compiled route. -/
def scanPrime (n : Nat) : Bool :=
  decide (2 ≤ n ∧ Sieve.leastFactor n = n)

/-- Under square-root coverage, one reblocked machine candidate is exactly one
word-safe source ladder step. -/
theorem flatObs_block_eq_loopE (n0 B q SL SU : Nat) (hB : 0 < B)
    (hn3 : 3 ≤ n0 + q)
    (hcover : n0 + q < (B + 2) * (B + 2)) :
    BlockedFold.block B (flatObs n0 B) (SL, SU, 0) q =
      ((loopE scanPrime 1 (n0 + q) SL SU).1,
       (loopE scanPrime 1 (n0 + q) SL SU).2, 0) := by
  have hn2 : 2 ≤ n0 + q := by omega
  have hiff := Sieve.spfScan_eq_zero_iff B (n0 + q) hn2 hcover
  rw [flatObs_block n0 B q SL SU hB]
  by_cases hs : Sieve.spfScan B (n0 + q) = 0
  · have hleast : Sieve.leastFactor (n0 + q) = n0 + q := hiff.mp hs
    have hp : scanPrime (n0 + q) = true := by
      simp [scanPrime, hn2, hleast]
    simp only [hs, if_pos]
    simp only [loopE, hp, if_pos]
    rw [incL_eq_wordSafe (n0 + q - 1) (by omega),
      incU_eq_wordSafe (n0 + q - 1) (by omega)]
  · have hleast : Sieve.leastFactor (n0 + q) ≠ n0 + q := by
      intro h
      exact hs (hiff.mpr h)
    have hp : scanPrime (n0 + q) = false := by
      simp [scanPrime, hn2, hleast]
    simp only [hs, if_false, Nat.add_zero]
    simp only [loopE, hp, Bool.false_eq_true, if_false]

/-- Folding candidate blocks is the guarded ladder fold.  This proof only
re-associates symbolic folds; it never evaluates the candidate range. -/
private theorem blocks_fold_eq_guarded (n0 B : Nat) (hB : 0 < B)
    (l : List Nat) (hlower : 3 ≤ n0)
    (hcover : ∀ q ∈ l, n0 + q < (B + 2) * (B + 2))
    (SL SU : Nat) :
    l.foldl (BlockedFold.block B (flatObs n0 B)) (SL, SU, 0) =
      let a := l.foldl
        (fun a q => stepGuarded scanPrime a (n0 + q)) (SL, SU)
      (a.1, a.2, 0) := by
  induction l generalizing SL SU with
  | nil => rfl
  | cons q rest ih =>
      have hq3 : 3 ≤ n0 + q := by omega
      have hqcover : n0 + q < (B + 2) * (B + 2) :=
        hcover q (by simp)
      have hblock := flatObs_block_eq_loopE n0 B q SL SU hB hq3 hqcover
      have hstep :
          BlockedFold.block B (flatObs n0 B) (SL, SU, 0) q =
            let a := stepGuarded scanPrime (SL, SU) (n0 + q)
            (a.1, a.2, 0) := by
        simpa only [loopE, stepGuarded, stepRef] using hblock
      rw [List.foldl_cons, List.foldl_cons, hstep]
      exact ih (fun r hr => hcover r (by simp [hr])) _ _

/-- The complete flat observable fold is exactly `loopE scanPrime`.  The
coverage hypothesis is a single endpoint bound and the proof cost is
independent of both `f` and `B`. -/
theorem flatObs_fold_eq_loopE (n0 f B SL SU : Nat) (hB : 0 < B)
    (hn0 : 3 ≤ n0) (hcover : n0 + f ≤ (B + 2) * (B + 2)) :
    (List.range (f * B)).foldl (flatObs n0 B) (SL, SU, 0) =
      ((loopE scanPrime f n0 SL SU).1,
       (loopE scanPrime f n0 SL SU).2, 0) := by
  rw [BlockedFold.foldl_range_mul]
  rw [loopE_eq_foldl,
    BlockedFold.foldl_range'_shift (stepGuarded scanPrime) f n0 (SL, SU)]
  exact blocks_fold_eq_guarded n0 B hB (List.range f) hn0
    (fun q hq => by
      have hqf := List.mem_range.mp hq
      omega) SL SU

/-! ## Complete scalar-program denotation -/

/-- Entry state after the two literal accumulator moves. -/
def ladderEntry (SL SU : Nat) : RegState :=
  (initialState.set rSL (SL % M)).set rSU (SU % M)

theorem ladderInit_denote (SL SU : Nat) :
    denoteInstrs 0 initialState
      [Instr.mov rSL (.lit SL), Instr.mov rSU (.lit SU)] =
      some (ladderEntry SL SU) := by
  rfl

/-- Machine-word room needed while the flat program executes.  It is stated
over symbolic prefixes so a compiled checkpoint campaign can establish it
without asking Lean to reduce the fold. -/
def FlatRoom (n0 f B SL SU : Nat) : Prop :=
  ∀ i, i < f * B →
    let z := (List.range i).foldl (flatObs n0 B) (SL, SU, 0)
    z.1 + incLWord (n0 + i / B - 1) < M ∧
      z.2.1 + incUWord (n0 + i / B - 1) < M

/-- Every symbolic flat prefix has a matching successful machine execution.
The proof is indexed by the prefix length and therefore carries exactly the
state produced at that index; no production fold is elaborated. -/
theorem ladderFold_denote (n0 f B SL SU j : Nat)
    (hB : 0 < B) (hflatM : f * B < M)
    (hBM : B + 1 < M) (hddM : (B + 1) * (B + 1) < M)
    (hn0 : 3 ≤ n0) (hn40 : n0 + f ≤ 2 ^ 40)
    (hSL : SL < M) (hSU : SU < M)
    (hroom : FlatRoom n0 f B SL SU) (hj : j ≤ f * B) :
    ∃ s,
      (List.range j).foldlM
          (fun s index => denoteInstrs index s (ladderBody n0 B))
          (ladderEntry SL SU) = some s ∧
      (s rSL, s rSU, s rAcc) =
        (List.range j).foldl (flatObs n0 B) (SL, SU, 0) ∧
      s rAcc < M := by
  induction j with
  | zero =>
      refine ⟨ladderEntry SL SU, rfl, ?_, by simp [ladderEntry, RegState.set,
        initialState, rSL, rSU, rAcc, M]⟩
      simp [ladderEntry, RegState.set, initialState, rSL, rSU, rAcc,
        Nat.mod_eq_of_lt hSL, Nat.mod_eq_of_lt hSU]
  | succ j ih =>
      have hjlt : j < f * B := by omega
      obtain ⟨s, hs, hobs, hacc⟩ := ih (by omega)
      let z := (List.range j).foldl (flatObs n0 B) (SL, SU, 0)
      have hroomj := hroom j hjlt
      change z.1 + incLWord (n0 + j / B - 1) < M ∧
        z.2.1 + incUWord (n0 + j / B - 1) < M at hroomj
      have hjM : j < M := Nat.lt_trans hjlt hflatM
      have hjdiv : j / B < f := by
        exact (Nat.div_lt_iff_lt_mul hB).mpr (by simpa [Nat.mul_comm] using hjlt)
      have hnM : n0 + j / B < M := by
        have hpow : 2 ^ 40 < M := by decide
        omega
      have hn3 : 3 ≤ n0 + j / B :=
        Nat.le_trans hn0 (Nat.le_add_right n0 (j / B))
      have hnle40 : n0 + j / B ≤ 2 ^ 40 := by omega
      have hrlt : j % B < B := Nat.mod_lt _ hB
      have hdlt : j % B + 2 < M := by omega
      have hdds : (j % B + 2) * (j % B + 2) < M := by
        have hle : j % B + 2 ≤ B + 1 := by omega
        exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hle hle) hddM
      have hsSL : s rSL = z.1 := congrArg Prod.fst hobs
      have hsSU : s rSU = z.2.1 := congrArg (fun x => x.2.1) hobs
      have hsAcc : s rAcc = z.2.2 := congrArg (fun x => x.2.2) hobs
      have hsSLM : s rSL < M := by rw [hsSL]; omega
      have hsSUM : s rSU < M := by rw [hsSU]; omega
      obtain ⟨s', hden, hvals⟩ := ladderBody_denote_flatRound n0 B j s
        hjM (by omega) hB hnM hdlt hdds hn3 hnle40 hsSLM hsSUM hacc
        (by simpa [hsSL] using hroomj.1)
        (by simpa [hsSU] using hroomj.2)
      refine ⟨s', ?_, ?_, ?_⟩
      · rw [List.range_succ, List.foldlM_append, hs]
        change (denoteInstrs j s (ladderBody n0 B)).bind some = some s'
        rw [hden]
        rfl
      · rw [List.range_succ, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        change (s' rSL, s' rSU, s' rAcc) = flatObs n0 B z j
        rw [flatObs, ← hsSL, ← hsSU, ← hsAcc]
        exact hvals
      · have hnext : scanNext (s rAcc) (n0 + j / B) (j % B + 2) < M :=
          scanNext_lt _ _ _ hacc hdlt
        have hs'Acc : s' rAcc =
            (flatRound n0 B j (s rSL) (s rSU) (s rAcc)).2.2 :=
          congrArg (fun x => x.2.2) hvals
        rw [hs'Acc]
        simp only [flatRound]
        split <;> omega

/-- The scalar machine computes the complete guarded ladder, provided its
symbolic prefixes fit in one word. -/
theorem ladderScalarProgram_denote (n0 f B SL SU out : Nat)
    (hOut : out = rSL ∨ out = rSU) (hB : 0 < B)
    (hflatM : f * B < M) (hBM : B + 1 < M)
    (hddM : (B + 1) * (B + 1) < M)
    (hn0 : 3 ≤ n0) (hn40 : n0 + f ≤ 2 ^ 40)
    (hcover : n0 + f ≤ (B + 2) * (B + 2))
    (hSL : SL < M) (hSU : SU < M)
    (hroom : FlatRoom n0 f B SL SU) :
    (ladderScalarProgram n0 f B SL SU out).denote =
      some (if out = rSL then (loopE scanPrime f n0 SL SU).1
        else (loopE scanPrime f n0 SL SU).2) := by
  obtain ⟨s, hfold, hobs, _⟩ := ladderFold_denote n0 f B SL SU (f * B)
    hB hflatM hBM hddM hn0 hn40 hSL hSU hroom (by omega)
  have hmath := flatObs_fold_eq_loopE n0 f B SL SU hB hn0 hcover
  have hall := hobs.trans hmath
  have hsL : s rSL = (loopE scanPrime f n0 SL SU).1 := by
    exact congrArg Prod.fst hall
  have hsU : s rSU = (loopE scanPrime f n0 SL SU).2 := by
    exact congrArg (fun x => x.2.1) hall
  simp only [ladderScalarProgram, Program.denote]
  rw [ladderInit_denote]
  change ((List.range (f * B)).foldlM
      (fun s index => denoteInstrs index s (ladderBody n0 B))
      (ladderEntry SL SU)).bind (fun s => some (s out)) = _
  rw [hfold]
  simp only [Option.bind_some]
  rcases hOut with rfl | rfl
  · simp [hsL]
  · simp only [rSL, rSU, Nat.reduceEqDiff, ↓reduceIte, Option.some.injEq]
    simpa only [rSU] using hsU

/-- The previously stated `LadderEncoding` obligation is discharged for the
proved scan predicate. -/
theorem ladderEncoding_scanPrime (n0 f B SL SU : Nat)
    (hB : 0 < B) (hflatM : f * B < M) (hBM : B + 1 < M)
    (hddM : (B + 1) * (B + 1) < M)
    (hn0 : 3 ≤ n0) (hn40 : n0 + f ≤ 2 ^ 40)
    (hcover : n0 + f ≤ (B + 2) * (B + 2))
    (hSL : SL < M) (hSU : SU < M)
    (hroom : FlatRoom n0 f B SL SU) :
    LadderEncoding scanPrime n0 f B SL SU := by
  constructor
  · rw [ladderProgram_denote]
    simpa using ladderScalarProgram_denote n0 f B SL SU rSL (Or.inl rfl)
      hB hflatM hBM hddM hn0 hn40 hcover hSL hSU hroom
  · rw [ladderProgram_denote]
    simpa [rSL, rSU] using
      ladderScalarProgram_denote n0 f B SL SU rSU (Or.inr rfl)
        hB hflatM hBM hddM hn0 hn40 hcover hSL hSU hroom

/-! The guarded flat route is now semantically complete.  Its production-cost
limitation is separate: scanning every divisor round is suitable for controls
and modest shards, while the full RS62 bundle still needs the verified
segmented prime-list/checkpoint program described in the campaign ledger. -/

end LeanCompCert.Ports.RS62LadderEncoding
