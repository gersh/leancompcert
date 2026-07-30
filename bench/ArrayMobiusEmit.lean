import LeanCompCert.Ports.ArrayMobius
import LeanCompCert.Verified.Rolled

/-!
Benchmark support for the array bridge.

Emits two artifacts that compute the *same* number — `L + Σ_{n<L} μ(n)` — by
two routes through the same proved fragment:

* `mobius-array` — the segmented Möbius sieve of `Ports.ArrayMobius`, an
  `AProgram`; one array, `O(L log log L)` work.
* `mobius-trial` — the memoryless equivalent: a `Reflect.Program` whose body
  recomputes `μ(n)` from scratch by trial division over the same prime table,
  unrolled into the loop body.  This is what the fragment could express
  *before* the array bridge existed.

Run with
`lake env lean --run bench/ArrayMobiusEmit.lean MODE L OUT EXPECTED`
where `MODE` is `array` or `trial`.  Emission only; no proof obligation is
discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArrayMobius

namespace Bench.ArrayMobiusEmit

/-! ## The memoryless trial-division baseline -/

/-- Registers: 0 = `accPos`, 1 = `accNeg`, 2 = `m`, 3 = `par`, 4 = `killed`,
5.. = scratch. -/
def trialRegCount : Nat := 16

/-- One unrolled trial-division step for prime `p`. -/
def trialStep (p : Nat) : List Instr :=
  [ .binop 5 .urem (.reg 2) (.lit p)        -- m % p
  , .binop 6 .eq (.reg 5) (.lit 0)          -- divides
  , .binop 7 .udiv (.reg 2) (.lit p)        -- m / p
  , .binop 8 .sub (.lit 1) (.reg 6)
  , .binop 9 .mul (.reg 6) (.reg 7)
  , .binop 10 .mul (.reg 8) (.reg 2)
  , .binop 2 .add (.reg 9) (.reg 10)        -- m := divides ? m/p : m
  , .binop 11 .urem (.reg 2) (.lit p)
  , .binop 12 .eq (.reg 11) (.lit 0)
  , .binop 13 .mul (.reg 6) (.reg 12)       -- p² ∣ n
  , .binop 4 .bor (.reg 4) (.reg 13)
  , .binop 3 .bxor (.reg 3) (.reg 6) ]

def trialBody (primes : List Nat) : List Instr :=
  [ .mov 2 .idx, .mov 3 (.lit 0), .mov 4 (.lit 0) ] ++
  primes.flatMap trialStep ++
  [ .binop 14 .gt (.reg 2) (.lit 1)         -- a prime factor above √L remains
  , .binop 3 .bxor (.reg 3) (.reg 14)
  , .binop 15 .sub (.lit 1) (.reg 4)        -- alive
  , .binop 5 .sub (.lit 1) (.reg 3)
  , .binop 6 .mul (.reg 15) (.reg 5)        -- μ = +1
  , .binop 7 .mul (.reg 15) (.reg 3)        -- μ = -1
  , .binop 0 .add (.reg 0) (.reg 6)
  , .binop 1 .add (.reg 1) (.reg 7) ]

def trialProgram (L : Nat) : Program := {
  regCount := trialRegCount
  loopCount := L
  init := []
  body := trialBody (smallPrimes L)
  epilogue :=
    [ .binop 5 .add (.reg 0) (.lit L)
    , .binop 6 .sub (.reg 5) (.reg 1) ]
  output := 6
}

/-! ## Drivers -/

def arrayDriver (name : String) (cells expected : Nat) : String :=
  "\nstatic uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "((uint64_t)(uintptr_t)cells);\n" ++
  "    return r == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

def scalarDriver (name : String) (expected : Nat) : String :=
  "\nint main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "();\n" ++
  "    return r == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

end Bench.ArrayMobiusEmit

open Bench.ArrayMobiusEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, lStr, out, expStr] =>
      let some L := lStr.toNat? | do IO.eprintln "bad L"; return 1
      let some expected := expStr.toNat? | do IO.eprintln "bad expected"; return 1
      match mode with
      | "array" =>
          let p := mobiusProgram L
          let name := s!"MobArr{L}"
          match p.emitRolled name with
          | .error errs => (for e in errs do IO.eprintln e); return 1
          | .ok src =>
              IO.FS.writeFile out (src ++ arrayDriver name p.arrayLen expected)
              IO.println s!"array L={L} arrayLen={p.arrayLen} loopCount={p.loopCount} denote-offset={L}"
              return 0
      | "trial" =>
          let p := trialProgram L
          let name := s!"MobTri{L}"
          match emitRolled p name with
          | .error errs => (for e in errs do IO.eprintln e); return 1
          | .ok src =>
              IO.FS.writeFile out (src ++ scalarDriver name expected)
              IO.println s!"trial L={L} primes={(smallPrimes L).length} bodySize={p.body.length}"
              return 0
      | _ => do IO.eprintln "mode must be array|trial"; return 1
  | _ => do IO.eprintln "usage: MODE L OUT EXPECTED"; return 1
