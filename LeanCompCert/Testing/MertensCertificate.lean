import LeanCompCert.Verified.Decide
import LeanCompCert.Lower.Pure

/-!
# A Goldbach-style fold certificate in the proved fragment

`ternary-goldbach-lean` discharges finite arithmetic facts with `native_decide`
certificates shaped like

```
theorem oddMertensLoAcc_ge : 125415339420275877467 ≤ oddMertensLoAcc := by
  native_decide
```

where `oddMertensLoAcc` folds a scaled integer floor-sum over a filtered range.
This module builds the same certificate shape inside LeanCompCert's proved
CCIR-to-restricted-C fragment: a bounded fold (unrolled through
`Proof.foldTrace`) whose per-iteration body filters with a proved `compare`
instruction and accumulates a scaled floor quotient with proved `udiv`, `mul`,
and `add` instructions.

The certified value is

```
Σ_{q odd, 1 ≤ q ≤ 99} ⌊2¹⁶ / q⌋ = 192509
```

The proposition is proved without `native_decide` and without any native
evaluation axiom, and the same packaged computation is emitted as restricted C
and compiled and executed by CompCert as an independent check.
-/

namespace LeanCompCert.Testing.MertensCertificate

set_option maxRecDepth 100000

open LeanCompCert
open LeanCompCert.Proof
open LeanCompCert.Verified

/-- Truncation height of the certified floor-sum. -/
def certHeight : Nat := 99

/-- Fixed-point scale `2¹⁶` for the integer-certified sum. -/
def certScale : Nat := 65536

/-- The certified value of the scaled odd-harmonic floor-sum. -/
def expectedValue : Nat := 192509

private def mkLocal (id : Nat) (type : CCIR.CCType := .u64) : CCIR.LocalDecl := {
  id := ⟨id⟩
  type
}

/--
One unrolled fold iteration for modulus `q`. CCIR's validator types
comparison results as `u8` and only permits mixed widths at shift counts, so
the parity filter flows through the term as a comparison-derived shift:

```
v1 : u64 = q
v2 : u64 = v1 & 1
v3 : u8  = (v2 == 0)      -- proved comparison instruction
v6 : u8  = v3 * 63        -- 63 when q is even, 0 when q is odd
v4 : u64 = certScale / v1 -- proved unsigned division
v5 : u64 = v4 >> v6       -- term survives only for odd q
v0 : u64 = v0 + v5
```

The comparison sits in the certified value path: `certScale / q < 2⁶³`, so
shifting by 63 zeroes the term exactly when the comparison says `q` is even.
-/
def iteration (q : Nat) : List StraightInstruction := [
  .assign (mkLocal 1) (.uintLit .u64 q),
  .binary (mkLocal 2) .bitAnd (.local ⟨1⟩) (.uintLit .u64 1),
  .compare (mkLocal 3 .u8) .eq (.local ⟨2⟩) (.uintLit .u64 0),
  .binary (mkLocal 6 .u8) .mul (.local ⟨3⟩) (.uintLit .u8 63),
  .binary (mkLocal 4) .udiv (.uintLit .u64 certScale) (.local ⟨1⟩),
  .binary (mkLocal 5) .lshr (.local ⟨4⟩) (.local ⟨6⟩),
  .binary (mkLocal 0) .add (.local ⟨0⟩) (.local ⟨5⟩)
]

/-- The full certificate trace: initialize the accumulator, then fold. -/
def instructions : List StraightInstruction :=
  .assign (mkLocal 0) (.uintLit .u64 0) ::
    foldTrace certHeight (fun index => iteration (index + 1))

def block : CCIR.Block := {
  id := ⟨0⟩
  instructions := (instructions.map StraightInstruction.toCCIR).toArray
  terminator := .return (some (.local ⟨0⟩))
}

def fn : CCIR.Function := {
  name := ⟨"MertensCert.oddFloorSum"⟩
  params := #[]
  result := .u64
  entry := block.id
  blocks := #[block]
  sourceDecl := some "Goldbach-style fold certificate"
}

/-- The statements produced by the production lowering of the trace. -/
def statements : List C.CStmt :=
  match lowerSequence fn instructions with
  | .ok statements => statements
  | .error _ => []

def computation : Computation := {
  fn
  block
  instructions
  statements
  output := ⟨0⟩
  wellFormed := by decide +kernel
  lowered := by rfl
}

/--
The Lean-level reference fold, in the shape of the goldbach repository's
`oddMertensLoAcc`: a `foldl` over a range with an oddness filter.
-/
def referenceSum : Nat :=
  (List.range (certHeight + 1)).foldl
    (fun acc q => if q % 2 = 1 then acc + certScale / q else acc) 0

def decision : Decision (referenceSum = expectedValue) := {
  computation
  acceptingValue := 192509
  specification := by decide +kernel
}

/--
The certificate, discharged through the proved compiler fragment instead of
`native_decide`. No native evaluation axiom is involved.
-/
theorem referenceSum_eq : referenceSum = expectedValue := by
  verified_decide using decision

/-- The goldbach-style lower-bound form of the same certificate. -/
theorem referenceSum_ge : expectedValue ≤ referenceSum :=
  referenceSum_eq ▸ Nat.le_refl _

/-- The generated-C model computes the same certified value. -/
theorem generated_c_model_returns : computation.targetResult = some 192509 := by
  rw [computation.result_preserved]
  exact Decision.prove (Decision.forResult computation 192509)
    (by decide +kernel)

def program : CCIR.Program := {
  functions := #[fn]
}

def mainC : String :=
  "\nint main(void)\n" ++
  "{\n" ++
  "    return l_MertensCert_oddFloorSum() == UINT64_C(192509) ? 0 : 1;\n" ++
  "}\n"

def emittedC : Except (Array String) String := do
  let (_, source) ← Lower.compileProgram .portable program
  pure (source ++ mainC)

end LeanCompCert.Testing.MertensCertificate
