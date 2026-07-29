import LeanCompCert.Verified.Package
import LeanCompCert.Testing.SquarefreeMertensCertificate

/-!
# The §14.1 certificate through the verified reflection bridge

This is the same odd-squarefree Mertens certificate as
`Testing.SquarefreeMertensCertificate`, but authored as a
`Verified.Reflect.Program` and discharged through the structural bridge
theorem: the kernel evaluates only the Lean-level denotation
(`Program.denote`, plain `Nat` arithmetic) — never the CCIR model. The
CCIR trace, its lowering, and the generated-C model are connected by the
once-and-for-all theorems `Program.evalCC_compile`,
`lowerSequence_correct`, and `Computation.result_preserved`.

Register map: `r0` lo, `r1` hi, `r2` q, `r3` parity, `r4` odd?, `r5`
squarefree mask, `r6`/`r7` scratch, `r8` totient, `r9`/`r10` factor
temps, `r11..r15` scaled-division temps, `r16`/`r17` masked term, `r18`
old lo, `r19` carry, `r20..r22` acceptance flags.
-/

namespace LeanCompCert.Testing.ReflectedCertificate

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Testing.SquarefreeMertensCertificate
  (certHeight expectedLo expectedHi expectedValue referenceSum)

set_option maxRecDepth 800000

private def maxU64 : Nat := 18446744073709551615

/-- Squarefree filter: `r5 &&= (q % d² ≠ 0)`. -/
def squarefreeMask (d : Nat) : List Instr := [
  .binop 6 .urem (.reg 2) (.lit (d * d)),
  .binop 7 .ne (.reg 6) (.lit 0),
  .binop 5 .band (.reg 5) (.reg 7)
]

/-- Totient factor: `r8 *= (p ∣ q) ? (p − 1) : 1`, branchless. -/
def totientFactor (p : Nat) : List Instr := [
  .binop 6 .urem (.reg 2) (.lit p),
  .binop 7 .eq (.reg 6) (.lit 0),
  .binop 9 .mul (.reg 7) (.lit (p - 2)),
  .binop 10 .add (.reg 9) (.lit 1),
  .binop 8 .mul (.reg 8) (.reg 10)
]

def program : Program := {
  regCount := 23
  loopCount := certHeight - 1
  init := [.mov 1 (.lit 1)]
  body :=
    [
      .binop 2 .add .idx (.lit 2),
      .binop 3 .band (.reg 2) (.lit 1),
      .binop 4 .eq (.reg 3) (.lit 1),
      .mov 5 (.lit 1)
    ] ++
    ([2, 3, 4, 5].flatMap squarefreeMask) ++
    [.mov 8 (.lit 1)] ++
    ([3, 5, 7, 11, 13, 17, 19, 23, 29].flatMap totientFactor) ++
    [
      .binop 11 .udiv (.lit maxU64) (.reg 8),
      .binop 12 .urem (.lit maxU64) (.reg 8),
      .binop 13 .sub (.reg 8) (.lit 1),
      .binop 14 .eq (.reg 12) (.reg 13),
      .binop 15 .add (.reg 11) (.reg 14),
      .binop 16 .band (.reg 4) (.reg 5),
      .binop 17 .mul (.reg 16) (.reg 15),
      .mov 18 (.reg 0),
      .binop 0 .add (.reg 18) (.reg 17),
      .binop 19 .lt (.reg 0) (.reg 18),
      .binop 1 .add (.reg 1) (.reg 19)
    ]
  epilogue := [
    .binop 20 .eq (.reg 0) (.lit expectedLo),
    .binop 21 .eq (.reg 1) (.lit expectedHi),
    .binop 22 .band (.reg 20) (.reg 21)
  ]
  output := 22
}

theorem program_wf : program.WF := by decide

/--
M1 packaging: every field of the `Computation` — including `wellFormed`
and `lowered` — is structural. The only decidable obligation was
`program_wf`, which is program-sized.
-/
def computation : Computation :=
  program.toComputation "MertensCert.reflectedOddSquarefreeMertens"
    program_wf

/--
The bridge instance for this certificate: acceptance is exactly the
denotation, with no CCIR-model evaluation.
-/
theorem returns_iff :
    computation.Returns ((1 : Nat) : Int) ↔ program.denote = some 1 :=
  returns_iff_denote program program_wf computation rfl rfl 1

def decision : Decision (referenceSum = expectedValue) := {
  computation
  acceptingValue := ((1 : Nat) : Int)
  specification := returns_iff.trans (by decide +kernel)
}

/--
The certificate: the kernel work is `program.denote` (a plain Lean fold)
plus the reference fold — the CCIR model is never evaluated.
-/
theorem referenceSum_eq : referenceSum = expectedValue :=
  Decision.prove decision (returns_iff.mpr (by decide +kernel))

/-- The generated-C model accepts, via the preservation chain alone. -/
theorem generated_c_model_accepts :
    computation.targetResult = some ((1 : Nat) : Int) := by
  rw [computation.result_preserved]
  exact returns_iff.mpr (by decide +kernel)

def mainC : String :=
  "\nint main(void)\n" ++
  "{\n" ++
  "    return l_MertensCert_reflectedOddSquarefreeMertens() == 1 ? 0 : 1;\n" ++
  "}\n"

def emittedC : Except (Array String) String := do
  let (_, source) ← Lower.compileProgram .portable
    { functions := #[computation.fn] }
  pure (source ++ mainC)

end LeanCompCert.Testing.ReflectedCertificate
