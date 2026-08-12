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
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.InstrBlock

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

/-- This helper is also the exact production slice. -/
theorem logAccumulatorCommitBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 139).take 9 = logAccumulatorCommitBody := by
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

#print axioms logJumpErrorInstrs_run
#print axioms logAccumulatorCommitInstrs_run
#print axioms logAccumulatorCommitBody_run

end LeanCompCert.Ports.R2SegSieve
