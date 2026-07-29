import LeanCompCert.Verified.Decide
import LeanCompCert.Lower.Pure

/-!
# A 2⁶⁴-scale fold certificate with a 128-bit accumulator

The production certificates in `ternary-goldbach-lean` scale their Mertens
sums by `2⁶⁴`, so the certified accumulators exceed 64 bits (the §14.1 bound
is `≈ 6.8 · 2⁶⁴`). This module certifies a fold at that exact scale inside
the proved straight-line fragment:

```
Σ_{q odd, 1 ≤ q ≤ 99} ⌊2⁶⁴ / q⌋ = 54192380775997480166 = 2·2⁶⁴ + lo
```

Everything wider than the machine word is built from proved 64-bit
instructions:

- `⌊2⁶⁴/q⌋` never fits a `u64` literal, so it is computed as
  `⌊(2⁶⁴−1)/q⌋ + [(2⁶⁴−1) mod q = q−1]`, with the increment decided by a
  proved comparison and widened by a proved cast;
- the accumulator is a `lo`/`hi` pair of `u64` locals; the carry out of the
  low word is the proved comparison `lo' < lo`, widened by a proved cast and
  added to the high word;
- the certificate output is an acceptance flag comparing both words against
  the certified constants, so the wide value sits entirely inside the
  verified computation.

The certificate is discharged by `verified_decide` with no native evaluation
axiom, and the same packaged computation is compiled and executed by CompCert.
-/

namespace LeanCompCert.Testing.WideMertensCertificate

set_option maxRecDepth 400000

open LeanCompCert
open LeanCompCert.Proof
open LeanCompCert.Verified

/-- Truncation height of the certified floor-sum. -/
def certHeight : Nat := 99

/-- The goldbach-repository fixed-point scale `2⁶⁴`. -/
def certScale : Nat := 2 ^ 64

/-- The certified 128-bit value, split into `u64` words. -/
def expectedLo : Nat := 17298892628578376934
def expectedHi : Nat := 2

/-- The certified value of the scaled odd-harmonic floor-sum. -/
def expectedValue : Nat := expectedHi * certScale + expectedLo

private def maxU64 : Nat := 18446744073709551615

private def mkLocal (id : Nat) (type : CCIR.CCType := .u64) : CCIR.LocalDecl := {
  id := ⟨id⟩
  type
}

/--
One unrolled fold iteration for modulus `q`:

```
v2  : u64 = q
v3  : u64 = v2 & 1
v4  : u8  = (v3 == 1)        -- odd? (proved comparison)
v5  : u64 = (u64) v4         -- proved widening cast
v6  : u64 = maxU64 / v2
v7  : u64 = maxU64 % v2
v8  : u64 = v2 - 1
v9  : u8  = (v7 == v8)       -- ⌊2⁶⁴/q⌋ increment (proved comparison)
v10 : u64 = (u64) v9
v11 : u64 = v6 + v10         -- ⌊2⁶⁴/q⌋
v12 : u64 = v5 * v11         -- term, masked to odd q
v13 : u64 = v0               -- old low word
v0  : u64 = v13 + v12        -- low word accumulate (mod 2⁶⁴)
v14 : u8  = (v0 < v13)       -- carry out (proved comparison)
v15 : u64 = (u64) v14
v1  : u64 = v1 + v15         -- high word accumulate
```
-/
def iteration (q : Nat) : List StraightInstruction := [
  .assign (mkLocal 2) (.uintLit .u64 q),
  .binary (mkLocal 3) .bitAnd (.local ⟨2⟩) (.uintLit .u64 1),
  .compare (mkLocal 4 .u8) .eq (.local ⟨3⟩) (.uintLit .u64 1),
  .cast (mkLocal 5) (.local ⟨4⟩),
  .binary (mkLocal 6) .udiv (.uintLit .u64 maxU64) (.local ⟨2⟩),
  .binary (mkLocal 7) .urem (.uintLit .u64 maxU64) (.local ⟨2⟩),
  .binary (mkLocal 8) .sub (.local ⟨2⟩) (.uintLit .u64 1),
  .compare (mkLocal 9 .u8) .eq (.local ⟨7⟩) (.local ⟨8⟩),
  .cast (mkLocal 10) (.local ⟨9⟩),
  .binary (mkLocal 11) .add (.local ⟨6⟩) (.local ⟨10⟩),
  .binary (mkLocal 12) .mul (.local ⟨5⟩) (.local ⟨11⟩),
  .assign (mkLocal 13) (.local ⟨0⟩),
  .binary (mkLocal 0) .add (.local ⟨13⟩) (.local ⟨12⟩),
  .compare (mkLocal 14 .u8) .ult (.local ⟨0⟩) (.local ⟨13⟩),
  .cast (mkLocal 15) (.local ⟨14⟩),
  .binary (mkLocal 1) .add (.local ⟨1⟩) (.local ⟨15⟩)
]

/--
The acceptance epilogue: both accumulator words must equal the certified
constants. The final `u8` flag is the certificate output.
-/
def epilogue : List StraightInstruction := [
  .compare (mkLocal 16 .u8) .eq (.local ⟨0⟩) (.uintLit .u64 expectedLo),
  .compare (mkLocal 17 .u8) .eq (.local ⟨1⟩) (.uintLit .u64 expectedHi),
  .binary (mkLocal 18 .u8) .bitAnd (.local ⟨16⟩) (.local ⟨17⟩)
]

/--
The full certificate trace.

The `q = 1` term is `⌊2⁶⁴/1⌋ = 2⁶⁴`, exactly one high-word unit — the same
special case as `oddMertensList`, whose `q = 1` member contributes
`1/φ(1) = 1` at the fixed-point scale. It does not fit the 64-bit term
local, so it initializes the accumulator as `(lo, hi) = (0, 1)` and the
in-circuit fold runs over `2 ≤ q ≤ certHeight`.
-/
def instructions : List StraightInstruction :=
  .assign (mkLocal 0) (.uintLit .u64 0) ::
    .assign (mkLocal 1) (.uintLit .u64 1) ::
      (foldTrace (certHeight - 1) (fun index => iteration (index + 2)) ++
        epilogue)

def block : CCIR.Block := {
  id := ⟨0⟩
  instructions := (instructions.map StraightInstruction.toCCIR).toArray
  terminator := .return (some (.local ⟨18⟩))
}

def fn : CCIR.Function := {
  name := ⟨"MertensCert.wideOddFloorSum"⟩
  params := #[]
  result := .u8
  entry := block.id
  blocks := #[block]
  sourceDecl := some "2^64-scale fold certificate with 128-bit accumulator"
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
  output := ⟨18⟩
  wellFormed := by decide +kernel
  lowered := by rfl
}

/--
The Lean-level reference fold at the production scale: the exact shape of
`oddMertensLoAcc` with `φ(q)` specialized to `q`.
-/
def referenceSum : Nat :=
  (List.range (certHeight + 1)).foldl
    (fun acc q => if q % 2 = 1 then acc + certScale / q else acc) 0

def decision : Decision (referenceSum = expectedValue) := {
  computation
  acceptingValue := 1
  specification := by decide +kernel
}

/--
The 128-bit certificate, discharged through the proved compiler fragment
instead of `native_decide`.
-/
theorem referenceSum_eq : referenceSum = expectedValue := by
  verified_decide using decision

/-- The goldbach-style lower-bound form: the sum exceeds `2·2⁶⁴`. -/
theorem referenceSum_ge : 2 * certScale ≤ referenceSum := by
  rw [referenceSum_eq]
  decide +kernel

/-- The generated-C model accepts with the same flag. -/
theorem generated_c_model_accepts : computation.targetResult = some 1 := by
  rw [computation.result_preserved]
  exact Decision.prove (Decision.forResult computation 1) (by decide +kernel)

def program : CCIR.Program := {
  functions := #[fn]
}

def mainC : String :=
  "\nint main(void)\n" ++
  "{\n" ++
  "    return l_MertensCert_wideOddFloorSum() == 1 ? 0 : 1;\n" ++
  "}\n"

def emittedC : Except (Array String) String := do
  let (_, source) ← Lower.compileProgram .portable program
  pure (source ++ mainC)

end LeanCompCert.Testing.WideMertensCertificate
