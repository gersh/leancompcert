import LeanCompCert.Verified.Package

/-!
# M2 acceptance: 128-bit products and dyadic division in a certificate

The certified quantity is the fixed-point sum

```
Σ_{n = 1..150} ⌊n·C / 2⁴⁸⌋,   C = 10¹⁸
```

whose per-element product `n·C` reaches `1.5·10²⁰ ≈ 8·2⁶⁴` — beyond the
machine word. The in-circuit computation is the 32-bit half-limb product
(four partial products, cross-sum carries detected by proved comparisons)
followed by a cross-limb dyadic shift — every step an already-proved
instruction, with the Lean-side theory provided by `Verified.Limb`
(`mulLimbs_val`). Packaging is M1's structural `Program.toComputation`;
the kernel evaluates only the denotation and the reference fold.
-/

namespace LeanCompCert.Testing.FixedPointCertificate

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect

set_option maxRecDepth 800000

/-- The fixed-point constant `C = 10¹⁸` and its 32-bit halves. -/
def bigC : Nat := 1000000000000000000
def bigC0 : Nat := 2808348672
def bigC1 : Nat := 232830643

def count : Nat := 150
def shift : Nat := 48
def expectedValue : Nat := 40234404

def mask32 : Nat := 4294967295

/--
Per-iteration body (`n = idx + 1`): half-limb 128-bit product `n·C`,
carry-corrected recombination, cross-limb `>> 48`, accumulate.
-/
def body : List Instr := [
  .binop 2 .add .idx (.lit 1),
  -- half-limb split of n (C's halves are literals)
  .binop 3 .band (.reg 2) (.lit mask32),
  .binop 4 .lshr (.reg 2) (.lit 32),
  -- four partial products, each < 2⁶⁴
  .binop 5 .mul (.reg 3) (.lit bigC0),
  .binop 6 .mul (.reg 3) (.lit bigC1),
  .binop 7 .mul (.reg 4) (.lit bigC0),
  .binop 8 .mul (.reg 4) (.lit bigC1),
  -- mid = p01 + p10 with carry detection (proved comparison)
  .binop 9 .add (.reg 6) (.reg 7),
  .binop 10 .lt (.reg 9) (.reg 6),
  -- lo = p00 + (mid << 32) with carry detection
  .binop 11 .shl (.reg 9) (.lit 32),
  .binop 12 .add (.reg 5) (.reg 11),
  .binop 13 .lt (.reg 12) (.reg 5),
  -- hi = p11 + (mid >> 32) + (carryMid << 32) + carryLo
  .binop 14 .lshr (.reg 9) (.lit 32),
  .binop 15 .shl (.reg 10) (.lit 32),
  .binop 16 .add (.reg 8) (.reg 14),
  .binop 16 .add (.reg 16) (.reg 15),
  .binop 16 .add (.reg 16) (.reg 13),
  -- dyadic division: (hi,lo) >> 48 = (lo >> 48) | (hi << 16)
  .binop 17 .lshr (.reg 12) (.lit shift),
  .binop 18 .shl (.reg 16) (.lit 16),
  .binop 19 .bor (.reg 17) (.reg 18),
  -- accumulate
  .binop 0 .add (.reg 0) (.reg 19)
]

def program : Program := {
  regCount := 20
  loopCount := count
  init := []
  body := body
  epilogue := []
  output := 0
}

theorem program_wf : program.WF := by decide

/-- M1 structural packaging — no trace-sized obligations. -/
def computation : Computation :=
  program.toComputation "FixedPoint.mulShiftSum" program_wf

/-- The reference fold: direct bignum arithmetic, no limbs. -/
def referenceSum : Nat :=
  (List.range count).foldl
    (fun acc k => acc + (((k + 1) * bigC) >>> shift)) 0

theorem returns_iff :
    computation.Returns ((expectedValue : Nat) : Int) ↔
      program.denote = some expectedValue :=
  toComputation_returns program "FixedPoint.mulShiftSum" program_wf
    expectedValue

def decision : Decision (referenceSum = expectedValue) := {
  computation
  acceptingValue := ((expectedValue : Nat) : Int)
  specification := returns_iff.trans (by decide +kernel)
}

/--
The M2 acceptance certificate: per-element 128-bit product and dyadic
division, discharged axiom-free through the proved fragment.
-/
theorem referenceSum_eq : referenceSum = expectedValue :=
  Decision.prove decision (returns_iff.mpr (by decide +kernel))

/-- The generated-C model agrees, via the structural chain alone. -/
theorem generated_c_model_returns :
    computation.targetResult = some ((expectedValue : Nat) : Int) := by
  rw [computation.result_preserved]
  exact returns_iff.mpr (by decide +kernel)

def mainC : String :=
  "\nint main(void)\n" ++
  "{\n" ++
  "    return l_FixedPoint_mulShiftSum() == UINT64_C(40234404) ? 0 : 1;\n" ++
  "}\n"

def emittedC : Except (Array String) String := do
  let (_, source) ← Lower.compileProgram .portable
    { functions := #[computation.fn] }
  pure (source ++ mainC)

end LeanCompCert.Testing.FixedPointCertificate
