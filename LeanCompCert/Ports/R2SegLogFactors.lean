import LeanCompCert.Ports.R2SegLogAccumulator

/-!
# Exact factor selection for an `R₂*` log event

This is the literal instruction bridge from the packed classifier mode and
decoded weights to the sign and two multiplicative inputs consumed by
`R2SegLogAccumulator`.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.InstrBlock

/-- Instructions 266--278 of the production log body. -/
def logFactorInstrs : List Instr :=
  [ .binop 266 .band (.reg 242) (.lit 1)
  , .binop 267 .eq (.reg 242) (.lit 0)
  , .binop 268 .eq (.reg 242) (.lit 2)
  , .binop 269 .eq (.reg 242) (.lit 3)
  , .binop 270 .sub (.reg 262) (.reg 265)
  , .binop 271 .mul (.reg 267) (.reg 270)
  , .binop 272 .add (.reg 263) (.reg 271)
  , .binop 273 .sub (.lit 1) (.reg 243)
  , .binop 274 .mul (.reg 273) (.reg 270)
  , .binop 275 .mul (.reg 268) (.reg 263)
  , .binop 276 .mul (.reg 269) (.reg 265)
  , .binop 277 .add (.reg 274) (.reg 275)
  , .binop 278 .add (.reg 277) (.reg 276) ]

def logFactorBody : List AInstr :=
  LeanCompCert.Verified.ArrayScalarBlock.lift logFactorInstrs

theorem logFactorBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 77).take 13 = logFactorBody := by
  rfl

/-- The literal selector produces exactly `ClassResult.jumpFactors`.  Mode
zero's packed first field is physically zero; the other three modes use it as
their first logarithmic factor. -/
theorem logFactorInstrs_run (k : Nat) (s : RegState)
    (mode first aux lnN : Nat)
    (hmode : mode ≤ 3) (hmode0 : mode = 0 → first = 0)
    (h242 : s 242 = mode)
    (h243 : s 243 = if 2 ≤ mode then 1 else 0)
    (h263 : s 263 = first) (h265 : s 265 = aux) (h262 : s 262 = lnN)
    (haux : aux ≤ lnN) (hlnM : lnN < M) (hfirstM : first < M)
    (hauxM : aux < M) (hsumM : first + (lnN - aux) < M) :
    let out := srun k s logFactorInstrs
    (out 266 == 1, out 272, out 278) =
      (ClassResult.jumpFactors ⟨true, mode, first, aux⟩ lnN) := by
  have hsub : denoteOp .sub lnN aux = some (lnN - aux) :=
    LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le haux hlnM
  have hm : mode = 0 ∨ mode = 1 ∨ mode = 2 ∨ mode = 3 := by omega
  rcases hm with rfl | rfl | rfl | rfl <;>
    simp_all [logFactorInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, ClassResult.jumpFactors, M,
      Nat.mod_eq_of_lt] <;> omega

/-- Array-state form of the exact factor selector. -/
theorem logFactorBody_run (k : Nat) (s : AState)
    (mode first aux lnN : Nat)
    (hmode : mode ≤ 3) (hmode0 : mode = 0 → first = 0)
    (h242 : s.regs 242 = mode)
    (h243 : s.regs 243 = if 2 ≤ mode then 1 else 0)
    (h263 : s.regs 263 = first) (h265 : s.regs 265 = aux)
    (h262 : s.regs 262 = lnN)
    (haux : aux ≤ lnN) (hlnM : lnN < M) (hfirstM : first < M)
    (hauxM : aux < M) (hsumM : first + (lnN - aux) < M) :
    let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s logFactorBody
    (out.regs 266 == 1, out.regs 272, out.regs 278) =
        (ClassResult.jumpFactors ⟨true, mode, first, aux⟩ lnN) ∧
      out.arr = s.arr := by
  have hrun := logFactorInstrs_run k s.regs mode first aux lnN
    hmode hmode0 h242 h243 h263 h265 h262 haux hlnM hfirstM hauxM hsumM
  dsimp only at hrun ⊢
  rw [logFactorBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨hrun, rfl⟩

#print axioms logFactorBody_eq_slice
#print axioms logFactorInstrs_run
#print axioms logFactorBody_run

end LeanCompCert.Ports.R2SegSieve
