import LeanCompCert.Ports.R2SegDenoteSegments
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.BlockDefined
import LeanCompCert.Verified.RegFrame

/-!
# Exact jump/error and accumulator slices for the `R₂*` log phase

This file isolates the two small arithmetic islands of `R2Cfg.logBody` that
compute a shifted jump plus its error charge and then commit that event to the
three carried accumulator registers.  The intervening comparison/majorant
instructions are intentionally left out: register-frame lemmas can transport
these exact values across them without normalizing the full log body.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.RegFrame

/-- Instructions 279--285: shifted jump followed by the uniform error charge.
-/
def logJumpErrorInstrs (S l2 : Nat) : List Instr :=
  [ .binop 279 .mul (.reg 272) (.reg 278)
  , .binop 280 .shl (.reg 279) (.reg 266)
  , .binop 281 .lshr (.reg 280) (.lit S)
  , .binop 282 .add (.reg rEx) (.lit 1)
  , .binop 283 .mul (.reg 282) (.lit l2)
  , .binop 284 .lshr (.reg 283) (.lit (S - 4))
  , .binop 285 .add (.reg 284) (.lit 2) ]

def logJumpErrorBody (S l2 : Nat) : List AInstr :=
  lift (logJumpErrorInstrs S l2)

/-- The helper is literally the production slice. -/
theorem logJumpErrorBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 90).take 7 =
      logJumpErrorBody c.sc (ln2Up c.sc) := by
  rfl

/-- The first arithmetic island computes exactly the natural jump and the
literal register charge, provided every intermediate fits one word. -/
theorem logJumpErrorInstrs_run (k : Nat) (s : RegState)
    (S l2 u v positive e : Nat)
    (hu : s 272 = u) (hv : s 278 = v) (hpositive : s 266 = positive)
    (he : s rEx = e)
    (hS : S < M) (hSm4 : S - 4 < M) (hl2 : l2 < M)
    (huv : u * v < M) (hshift : ((u * v) <<< positive) < M)
    (he1 : e + 1 < M) (henum : (e + 1) * l2 < M)
    (hcharge : ((e + 1) * l2 / 2 ^ (S - 4)) + 2 < M) :
    let out := srun k s (logJumpErrorInstrs S l2)
    out 281 = ((u * v) <<< positive) / 2 ^ S ∧
      out 285 = ((e + 1) * l2) / 2 ^ (S - 4) + 2 := by
  have he' : s 186 = e := by simpa [rEx] using he
  have hjumpM : ((u * v) <<< positive) / 2 ^ S < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hshift
  have hcoreM : (e + 1) * l2 / 2 ^ (S - 4) < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) henum
  simp [logJumpErrorInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, rEx, he', Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hS, Nat.mod_eq_of_lt hSm4, Nat.mod_eq_of_lt hl2,
    Nat.mod_eq_of_lt huv, Nat.mod_eq_of_lt hshift,
    Nat.mod_eq_of_lt he1, Nat.mod_eq_of_lt henum,
    Nat.mod_eq_of_lt hjumpM, Nat.mod_eq_of_lt hcoreM,
    Nat.mod_eq_of_lt hcharge, hu, hv, hpositive]

/-- Array-state form of the jump/error island, including every frame needed
by the later commit. -/
theorem logJumpErrorBody_run (k : Nat) (s : AState)
    (S l2 u v positive e : Nat)
    (hu : s.regs 272 = u) (hv : s.regs 278 = v)
    (hpositive : s.regs 266 = positive) (he : s.regs rEx = e)
    (hS : S < M) (hSm4 : S - 4 < M) (hl2 : l2 < M)
    (huv : u * v < M) (hshift : ((u * v) <<< positive) < M)
    (he1 : e + 1 < M) (henum : (e + 1) * l2 < M)
    (hcharge : ((e + 1) * l2 / 2 ^ (S - 4)) + 2 < M) :
    let out := arun k s (logJumpErrorBody S l2)
    out.regs 281 = ((u * v) <<< positive) / 2 ^ S ∧
      out.regs 285 = ((e + 1) * l2) / 2 ^ (S - 4) + 2 ∧
      out.regs 266 = s.regs 266 ∧ out.regs 247 = s.regs 247 ∧
      out.regs rErr = s.regs rErr ∧ out.regs rTerms = s.regs rTerms ∧
      out.arr = s.arr := by
  have hrun := logJumpErrorInstrs_run k s.regs S l2 u v positive e
    hu hv hpositive he hS hSm4 hl2 huv hshift he1 henum hcharge
  dsimp only at hrun ⊢
  rw [logJumpErrorBody,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact
    ⟨hrun.1, hrun.2,
     srun_frame k 266 (logJumpErrorInstrs S l2) (by rfl) s.regs,
     srun_frame k 247 (logJumpErrorInstrs S l2) (by rfl) s.regs,
     srun_frame k rErr (logJumpErrorInstrs S l2) (by rfl) s.regs,
     srun_frame k rTerms (logJumpErrorInstrs S l2) (by rfl) s.regs,
     rfl⟩

/-- The 42 instructions between the jump/error calculation and its commit.
They advance and test the linear/majorant state but do not alter the event
payload or the two already-carried error/count words. -/
def logBetweenJumpAndCommitBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 97).take 42

theorem logBetweenJumpAndCommitBody_frame (c : R2Cfg) (k : Nat) (s : AState) :
    let out := arun k s (logBetweenJumpAndCommitBody c)
    out.regs 266 = s.regs 266 ∧ out.regs 247 = s.regs 247 ∧
      out.regs 281 = s.regs 281 ∧ out.regs 285 = s.regs 285 ∧
      out.regs rErr = s.regs rErr ∧ out.regs rTerms = s.regs rTerms ∧
      out.arr = s.arr := by
  dsimp only
  exact
    ⟨arun_frame k 266 (logBetweenJumpAndCommitBody c) (by rfl) s,
     arun_frame k 247 (logBetweenJumpAndCommitBody c) (by rfl) s,
     arun_frame k 281 (logBetweenJumpAndCommitBody c) (by rfl) s,
     arun_frame k 285 (logBetweenJumpAndCommitBody c) (by rfl) s,
     arun_frame k rErr (logBetweenJumpAndCommitBody c) (by rfl) s,
     arun_frame k rTerms (logBetweenJumpAndCommitBody c) (by rfl) s,
     LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
       k (logBetweenJumpAndCommitBody c) s (by rfl)⟩

/-- Instructions 316--320 plus the term counter commit. -/
def logAccumulatorCommitInstrs : List Instr :=
  [ .binop 316 .mul (.reg 266) (.reg 247)
  , .binop 317 .mul (.reg 316) (.reg 281)
  , .binop 318 .sub (.reg 247) (.reg 316)
  , .binop 319 .mul (.reg 318) (.reg 281)
  , .binop rD .add (.reg rD) (.reg 317)
  , .binop rD .sub (.reg rD) (.reg 319)
  , .binop 320 .mul (.reg 285) (.reg 247)
  , .binop rErr .add (.reg rErr) (.reg 320)
  , .binop rTerms .add (.reg rTerms) (.reg 247) ]

def logAccumulatorCommitBody : List AInstr :=
  lift logAccumulatorCommitInstrs

/-- The seven-instruction negative-underflow audit inserted immediately before
the signed accumulator commit.  It compares the already-computed jump with
the post-linear accumulator, gates the bit by both the negative-event and
finish bits, then increments the aggregate and dedicated counters. -/
def logUnderflowAuditInstrs : List Instr :=
  [ .binop 327 .gt (.reg 281) (.reg rD)
  , .binop 328 .eq (.reg 266) (.lit 0)
  , .binop 329 .mul (.reg 327) (.reg 328)
  , .binop 346 .eq (.reg 247) (.lit 1)
  , .binop 329 .mul (.reg 329) (.reg 346)
  , .binop rViol .add (.reg rViol) (.reg 329)
  , .binop rVSub .add (.reg rVSub) (.reg 329) ]

def logUnderflowAuditBody : List AInstr :=
  lift logUnderflowAuditInstrs

/-- The audit is the exact strengthened-production slice. -/
theorem logUnderflowAuditBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 139).take 7 = logUnderflowAuditBody := by
  rfl

/-- The audit does not alter the event arithmetic or the sieve array. -/
theorem logUnderflowAuditBody_frame (k : Nat) (s : AState) :
    let out := arun k s logUnderflowAuditBody
    out.regs rD = s.regs rD ∧ out.regs rErr = s.regs rErr ∧
      out.regs rTerms = s.regs rTerms ∧ out.regs 247 = s.regs 247 ∧
      out.regs 266 = s.regs 266 ∧ out.regs 281 = s.regs 281 ∧
      out.regs 285 = s.regs 285 ∧ out.arr = s.arr := by
  dsimp only
  exact
    ⟨arun_frame k rD logUnderflowAuditBody (by rfl) s,
     arun_frame k rErr logUnderflowAuditBody (by rfl) s,
     arun_frame k rTerms logUnderflowAuditBody (by rfl) s,
     arun_frame k 247 logUnderflowAuditBody (by rfl) s,
     arun_frame k 266 logUnderflowAuditBody (by rfl) s,
     arun_frame k 281 logUnderflowAuditBody (by rfl) s,
     arun_frame k 285 logUnderflowAuditBody (by rfl) s,
     LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
       k logUnderflowAuditBody s (by rfl)⟩

/-- The three pieces form the exact production interval from instruction 279
through the term-counter commit. -/
theorem logJumpThroughCommitBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 90).take 65 =
      logJumpErrorBody c.sc (ln2Up c.sc) ++
        logBetweenJumpAndCommitBody c ++ logUnderflowAuditBody ++
          logAccumulatorCommitBody := by
  rfl

/-- This helper is also the exact production slice. -/
theorem logAccumulatorCommitBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 146).take 9 = logAccumulatorCommitBody := by
  rfl

/-- On a finished event, the commit island performs the selected signed jump,
adds the exact charge, and increments the term count. -/
theorem logAccumulatorCommitInstrs_run (k : Nat) (s : RegState)
    (positive : Bool) (d err terms term charge : Nat)
    (hfin : s 247 = 1)
    (hpositive : s 266 = if positive then 1 else 0)
    (hd : s rD = d) (herr : s rErr = err) (hterms : s rTerms = terms)
    (hterm : s 281 = term) (hcharge : s 285 = charge)
    (hsub : positive = false → term ≤ d)
    (hdadd : positive = true → d + term < M)
    (hdM : d < M) (htermM : term < M) (hchargeM : charge < M)
    (herradd : err + charge < M) (htermsadd : terms + 1 < M) :
    let out := srun k s logAccumulatorCommitInstrs
    out rD = (if positive then d + term else d - term) ∧
      out rErr = err + charge ∧ out rTerms = terms + 1 := by
  have hd' : s 180 = d := by simpa [rD] using hd
  have herr' : s 181 = err := by simpa [rErr] using herr
  have hterms' : s 183 = terms := by simpa [rTerms] using hterms
  cases positive
  · have htd : term ≤ d := hsub rfl
    have hsubWord : denoteOp .sub d term = some (d - term) :=
      LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le htd hdM
    have hsub10 : denoteOp .sub 1 0 = some 1 :=
      LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le (by omega)
        (by simp [M])
    simp_all [logAccumulatorCommitInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, rD, rErr, rTerms,
      Nat.mod_eq_of_lt]
  · have hdterm : d + term < M := hdadd rfl
    have hsub11 : denoteOp .sub 1 1 = some 0 :=
      LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le (by omega)
        (by simp [M])
    have hsub0 : denoteOp .sub (d + term) 0 = some (d + term) :=
      LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le (by omega) hdterm
    have hsub0raw : (d + term + (M - 0)) % M = d + term :=
      Option.some.inj hsub0
    have hgateZero : (1 + (M - 1 % M)) * term % M = 0 := by
      have h1M : 1 < M := by simp [M]
      rw [Nat.mod_eq_of_lt h1M]
      have hMpos : 0 < M := by simp [M]
      rw [show 1 + (M - 1) = M by omega, Nat.mul_mod_right]
    simp_all [logAccumulatorCommitInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, rD, rErr, rTerms,
      Nat.mod_eq_of_lt]

/-- Array-machine form of `logAccumulatorCommitInstrs_run`.  Besides the
three exact carried-register updates it records that the production scalar
slice leaves every sieve cell unchanged. -/
theorem logAccumulatorCommitBody_run (k : Nat) (s : AState)
    (positive : Bool) (d err terms term charge : Nat)
    (hfin : s.regs 247 = 1)
    (hpositive : s.regs 266 = if positive then 1 else 0)
    (hd : s.regs rD = d) (herr : s.regs rErr = err)
    (hterms : s.regs rTerms = terms)
    (hterm : s.regs 281 = term) (hcharge : s.regs 285 = charge)
    (hsub : positive = false → term ≤ d)
    (hdadd : positive = true → d + term < M)
    (hdM : d < M) (htermM : term < M) (hchargeM : charge < M)
    (herradd : err + charge < M) (htermsadd : terms + 1 < M) :
    let out := arun k s logAccumulatorCommitBody
    out.regs rD = (if positive then d + term else d - term) ∧
      out.regs rErr = err + charge ∧ out.regs rTerms = terms + 1 ∧
      out.arr = s.arr := by
  have hrun := logAccumulatorCommitInstrs_run k s.regs positive
    d err terms term charge hfin hpositive hd herr hterms hterm hcharge
    hsub hdadd hdM htermM hchargeM herradd htermsadd
  dsimp only at hrun ⊢
  rw [logAccumulatorCommitBody,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨hrun.1, hrun.2.1, hrun.2.2, rfl⟩

/-- Exact composition from the product registers through the signed carried
state.  The sole `d` hypothesis names the intended post-linear accumulator
produced by the intervening block; all event payload, error, count, and array
facts are derived here from the literal instruction stream. -/
theorem logJumpThroughCommitBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (positive : Bool) (u v e d err terms : Nat)
    (hu : s.regs 272 = u) (hv : s.regs 278 = v)
    (hpositive : s.regs 266 = if positive then 1 else 0)
    (he : s.regs rEx = e) (hfin : s.regs 247 = 1)
    (herr : s.regs rErr = err) (hterms : s.regs rTerms = terms)
    (hS : c.sc < M) (hSm4 : c.sc - 4 < M) (hl2 : ln2Up c.sc < M)
    (huv : u * v < M)
    (hshift : ((u * v) <<< (if positive then 1 else 0)) < M)
    (he1 : e + 1 < M) (henum : (e + 1) * ln2Up c.sc < M)
    (hcharge : ((e + 1) * ln2Up c.sc / 2 ^ (c.sc - 4)) + 2 < M)
    (hd : (arun k (arun k s (logJumpErrorBody c.sc (ln2Up c.sc)))
      (logBetweenJumpAndCommitBody c)).regs rD = d)
    (hsub : positive = false →
      ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc ≤ d)
    (hdadd : positive = true →
      d + ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc < M)
    (hdM : d < M)
    (htermM : ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc < M)
    (herradd : err +
      (((e + 1) * ln2Up c.sc) / 2 ^ (c.sc - 4) + 2) < M)
    (htermsadd : terms + 1 < M) :
    let term := ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc
    let charge := ((e + 1) * ln2Up c.sc) / 2 ^ (c.sc - 4) + 2
    let out := arun k s
      (logJumpErrorBody c.sc (ln2Up c.sc) ++
        logBetweenJumpAndCommitBody c ++ logUnderflowAuditBody ++
          logAccumulatorCommitBody)
    out.regs rD = (if positive then d + term else d - term) ∧
      out.regs rErr = err + charge ∧ out.regs rTerms = terms + 1 ∧
      out.arr = s.arr := by
  dsimp only
  let bit := if positive then 1 else 0
  let term := ((u * v) <<< bit) / 2 ^ c.sc
  let charge := ((e + 1) * ln2Up c.sc) / 2 ^ (c.sc - 4) + 2
  let afterJump := arun k s (logJumpErrorBody c.sc (ln2Up c.sc))
  let beforeAudit := arun k afterJump (logBetweenJumpAndCommitBody c)
  let beforeCommit := arun k beforeAudit logUnderflowAuditBody
  have hjump := logJumpErrorBody_run k s c.sc (ln2Up c.sc) u v bit e
    hu hv hpositive he hS hSm4 hl2 huv hshift he1 henum hcharge
  dsimp only at hjump
  have hframe := logBetweenJumpAndCommitBody_frame c k afterJump
  dsimp only at hframe
  have haudit := logUnderflowAuditBody_frame k beforeAudit
  dsimp only at haudit
  have hchargeM : charge < M := by
    simpa only [charge] using hcharge
  have hcommit := logAccumulatorCommitBody_run k beforeCommit positive
    d err terms term charge
    (haudit.2.2.2.1.trans (hframe.2.1.trans (hjump.2.2.2.1.trans hfin)))
    (haudit.2.2.2.2.1.trans (hframe.1.trans
      (hjump.2.2.1.trans hpositive)))
    (haudit.1.trans hd)
    (haudit.2.1.trans
      (hframe.2.2.2.2.1.trans (hjump.2.2.2.2.1.trans herr)))
    (haudit.2.2.1.trans
      (hframe.2.2.2.2.2.1.trans (hjump.2.2.2.2.2.1.trans hterms)))
    (haudit.2.2.2.2.2.1.trans (hframe.2.2.1.trans hjump.1))
    (haudit.2.2.2.2.2.2.1.trans (hframe.2.2.2.1.trans hjump.2.1))
    hsub hdadd hdM htermM hchargeM
    herradd htermsadd
  dsimp only at hcommit
  rw [arun_append, arun_append, arun_append]
  exact ⟨hcommit.1, hcommit.2.1, hcommit.2.2.1,
    hcommit.2.2.2.trans
      (haudit.2.2.2.2.2.2.2.trans
        (hframe.2.2.2.2.2.2.trans hjump.2.2.2.2.2.2))⟩

#print axioms logJumpErrorInstrs_run
#print axioms logJumpErrorBody_run
#print axioms logBetweenJumpAndCommitBody_frame
#print axioms logUnderflowAuditBody_eq_slice
#print axioms logUnderflowAuditBody_frame
#print axioms logJumpThroughCommitBody_eq_slice
#print axioms logAccumulatorCommitInstrs_run
#print axioms logAccumulatorCommitBody_run
#print axioms logJumpThroughCommitBody_run

end LeanCompCert.Ports.R2SegSieve
