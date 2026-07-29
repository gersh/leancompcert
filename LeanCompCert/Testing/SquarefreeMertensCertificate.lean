import LeanCompCert.Verified.Decide
import LeanCompCert.Lower.Pure

/-!
# The §14.1 odd squarefree Mertens shape in the proved fragment

`ternary-goldbach-lean`'s `oddMertensLoAcc_ge` certificate bounds

```
Σ_{q ≤ 150000, q odd, squarefree} ⌊2⁶⁴ / φ(q)⌋
```

with the per-element work done by trial division (`Nat.minSqFac` for
squarefreeness, duplicate-free prime factor lists for `φ`). This module
certifies the same quantity, with the same per-element mathematics computed
inside the proved CCIR-to-restricted-C fragment, at reduced height
`q ≤ 30`:

- the squarefree filter is in-circuit trial division: for every `d` with
  `d² ≤ 30`, a proved `urem`/comparison pair masks out `d² ∣ q`;
- `φ(q)` is the in-circuit product `Π_{p ∣ q} (p − 1)` over the odd primes
  `p ≤ 30`, each factor selected branchlessly by a proved comparison and
  cast (the prime list is fixed at trace-construction time, exactly as the
  goldbach certificate fixes its modulus list);
- terms are scaled by `2⁶⁴` and accumulated in a 128-bit `lo`/`hi` pair with
  proved carry comparisons, and the `q = 1` term (`2⁶⁴/φ(1) = 2⁶⁴`, one full
  high word) initializes the accumulator, mirroring `oddMertensList`'s
  explicit `q = 1` member.

For non-squarefree `q` the in-circuit product is `φ` of the radical rather
than `φ(q)`, and those terms are exactly the ones removed by the squarefree
mask — the same division of labor as the goldbach certificate, whose fast
totient is only claimed on squarefree inputs. Over this height the reference
fold provably coincides with the true odd-squarefree Mertens sum.

The certificate is discharged by `verified_decide` with no native evaluation
axiom, and the packaged computation is compiled and executed by CompCert.
-/

namespace LeanCompCert.Testing.SquarefreeMertensCertificate

set_option maxRecDepth 800000

open LeanCompCert
open LeanCompCert.Proof
open LeanCompCert.Verified

/-- Truncation height of the certified sum. -/
def certHeight : Nat := 30

/-- The goldbach fixed-point scale `2⁶⁴`. -/
def certScale : Nat := 2 ^ 64

/-- Trial divisors for the squarefree filter: `d` with `d² ≤ certHeight`. -/
def squareDivisors : List Nat := [2, 3, 4, 5]

/-- The odd primes up to `certHeight`, fixed at trace-construction time. -/
def oddPrimes : List Nat := [3, 5, 7, 11, 13, 17, 19, 23, 29]

/-- The certified 128-bit value, split into `u64` words. -/
def expectedLo : Nat := 9362787364540279089
def expectedHi : Nat := 2

def expectedValue : Nat := expectedHi * certScale + expectedLo

private def maxU64 : Nat := 18446744073709551615

private def mkLocal (id : Nat) (type : CCIR.CCType := .u64) : CCIR.LocalDecl := {
  id := ⟨id⟩
  type
}

/-- In-circuit squarefree mask: `v5 &= (q % d² ≠ 0)` for each divisor. -/
def squarefreeMask (d : Nat) : List StraightInstruction := [
  .binary (mkLocal 6) .urem (.local ⟨2⟩) (.uintLit .u64 (d * d)),
  .compare (mkLocal 7 .u8) .eq (.local ⟨6⟩) (.uintLit .u64 0),
  .binary (mkLocal 8 .u8) .bitXor (.local ⟨7⟩) (.uintLit .u8 1),
  .binary (mkLocal 5 .u8) .bitAnd (.local ⟨5⟩) (.local ⟨8⟩)
]

/-- In-circuit totient factor: `v9 *= (p ∣ q) ? (p − 1) : 1`, branchless. -/
def totientFactor (p : Nat) : List StraightInstruction := [
  .binary (mkLocal 6) .urem (.local ⟨2⟩) (.uintLit .u64 p),
  .compare (mkLocal 7 .u8) .eq (.local ⟨6⟩) (.uintLit .u64 0),
  .cast (mkLocal 10) (.local ⟨7⟩),
  .binary (mkLocal 11) .mul (.local ⟨10⟩) (.uintLit .u64 (p - 2)),
  .binary (mkLocal 12) .add (.local ⟨11⟩) (.uintLit .u64 1),
  .binary (mkLocal 9) .mul (.local ⟨9⟩) (.local ⟨12⟩)
]

/--
One unrolled fold iteration for modulus `q`: parity mask, squarefree trial
division, totient product, `⌊2⁶⁴/φ⌋` with comparison-decided increment, and
128-bit accumulation.
-/
def iteration (q : Nat) : List StraightInstruction :=
  [
    -- q and the oddness mask
    .assign (mkLocal 2) (.uintLit .u64 q),
    .binary (mkLocal 3) .bitAnd (.local ⟨2⟩) (.uintLit .u64 1),
    .compare (mkLocal 4 .u8) .eq (.local ⟨3⟩) (.uintLit .u64 1),
    -- squarefree mask accumulator
    .assign (mkLocal 5 .u8) (.uintLit .u8 1)
  ] ++
  (squareDivisors.flatMap squarefreeMask) ++
  -- totient product accumulator
  [.assign (mkLocal 9) (.uintLit .u64 1)] ++
  (oddPrimes.flatMap totientFactor) ++
  [
    -- dfull = ⌊2⁶⁴/φ⌋ = ⌊(2⁶⁴−1)/φ⌋ + [(2⁶⁴−1) mod φ = φ−1]
    .binary (mkLocal 13) .udiv (.uintLit .u64 maxU64) (.local ⟨9⟩),
    .binary (mkLocal 14) .urem (.uintLit .u64 maxU64) (.local ⟨9⟩),
    .binary (mkLocal 15) .sub (.local ⟨9⟩) (.uintLit .u64 1),
    .compare (mkLocal 16 .u8) .eq (.local ⟨14⟩) (.local ⟨15⟩),
    .cast (mkLocal 17) (.local ⟨16⟩),
    .binary (mkLocal 18) .add (.local ⟨13⟩) (.local ⟨17⟩),
    -- masked term
    .binary (mkLocal 19 .u8) .bitAnd (.local ⟨4⟩) (.local ⟨5⟩),
    .cast (mkLocal 20) (.local ⟨19⟩),
    .binary (mkLocal 21) .mul (.local ⟨20⟩) (.local ⟨18⟩),
    -- 128-bit accumulate
    .assign (mkLocal 22) (.local ⟨0⟩),
    .binary (mkLocal 0) .add (.local ⟨22⟩) (.local ⟨21⟩),
    .compare (mkLocal 23 .u8) .ult (.local ⟨0⟩) (.local ⟨22⟩),
    .cast (mkLocal 24) (.local ⟨23⟩),
    .binary (mkLocal 1) .add (.local ⟨1⟩) (.local ⟨24⟩)
  ]

/-- Acceptance epilogue over both accumulator words. -/
def epilogue : List StraightInstruction := [
  .compare (mkLocal 25 .u8) .eq (.local ⟨0⟩) (.uintLit .u64 expectedLo),
  .compare (mkLocal 26 .u8) .eq (.local ⟨1⟩) (.uintLit .u64 expectedHi),
  .binary (mkLocal 27 .u8) .bitAnd (.local ⟨25⟩) (.local ⟨26⟩)
]

/--
The full certificate trace. `(lo, hi)` starts at `(0, 1)`: the `q = 1` term
is `2⁶⁴/φ(1) = 2⁶⁴`, exactly one high word, the same explicit `q = 1`
membership as `oddMertensList`. The in-circuit fold covers `2 ≤ q ≤ 30`.
-/
def instructions : List StraightInstruction :=
  .assign (mkLocal 0) (.uintLit .u64 0) ::
    .assign (mkLocal 1) (.uintLit .u64 1) ::
      (foldTrace (certHeight - 1) (fun index => iteration (index + 2)) ++
        epilogue)

def block : CCIR.Block := {
  id := ⟨0⟩
  instructions := (instructions.map StraightInstruction.toCCIR).toArray
  terminator := .return (some (.local ⟨27⟩))
}

def fn : CCIR.Function := {
  name := ⟨"MertensCert.oddSquarefreeMertens"⟩
  params := #[]
  result := .u8
  entry := block.id
  blocks := #[block]
  sourceDecl := some "odd squarefree Mertens certificate (goldbach section 14.1 shape)"
}

def statements : List C.CStmt :=
  match lowerSequence fn instructions with
  | .ok statements => statements
  | .error _ => []

def computation : Computation := {
  fn
  block
  instructions
  statements
  output := ⟨27⟩
  wellFormed := by decide +kernel
  lowered := by rfl
}

/-- Reference squarefree filter: trial division by every `d` with `d² ≤ 30`. -/
def refSquarefree (q : Nat) : Bool :=
  squareDivisors.all fun d => q % (d * d) != 0

/-- Reference fast totient: `Π_{p ∣ q} (p − 1)` over the fixed prime list. -/
def refPhi (q : Nat) : Nat :=
  oddPrimes.foldl (fun acc p => if q % p == 0 then acc * (p - 1) else acc) 1

/--
The Lean-level reference fold: the `oddMertensLoAcc` shape at height 30,
including the `q = 1` term.
-/
def referenceSum : Nat :=
  certScale +
    ((List.range (certHeight + 1)).drop 2).foldl
      (fun acc q =>
        if q % 2 = 1 && refSquarefree q then acc + certScale / refPhi q
        else acc)
      0

def decision : Decision (referenceSum = expectedValue) := {
  computation
  acceptingValue := 1
  specification := by decide +kernel
}

/--
The §14.1-shaped certificate, discharged through the proved compiler
fragment instead of `native_decide`.
-/
theorem referenceSum_eq : referenceSum = expectedValue := by
  verified_decide using decision

/-- The goldbach-style lower-bound form. -/
theorem referenceSum_ge : expectedValue ≤ referenceSum :=
  referenceSum_eq ▸ Nat.le_refl _

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
  "    return l_MertensCert_oddSquarefreeMertens() == 1 ? 0 : 1;\n" ++
  "}\n"

def emittedC : Except (Array String) String := do
  let (_, source) ← Lower.compileProgram .portable program
  pure (source ++ mainC)

end LeanCompCert.Testing.SquarefreeMertensCertificate
