import LeanCompCert.Ports.ArraySegSieve

/-!
# The transparent model of one `mobiusLiveResidue` step

`mobiusLiveResidue` is fifty straight-line register instructions.  This module
transcribes them into plain `Nat` arithmetic — every `let` below is one
instruction, the `% M` truncations included — so that

* `Ports/MobiusResidueRealisation.lean` can prove that the block *denotes*
  this model, and
* `Ports/MobiusResidueArith.lean` can prove that this model *is* the
  fixed-point arithmetic the residue is named after,

with no proof having to do both at once.
-/

namespace LeanCompCert.Ports.MobiusResidueRealisation

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

/-! ## The transparent model of one residue step

Every `let` below is one instruction of `mobiusLiveResidue`, transcribed
literally — the `% M` truncations included.
-/

/-- The four signals the sieve core leaves for the residue: the current
integer `n` (register `65`), the two `μ` indicators (registers `79`, `80`)
and the main-accumulation gate (register `133`). -/
structure Sig where
  n : Nat
  pos : Nat
  neg : Nat
  gate : Nat
  deriving Repr, DecidableEq

/-- The residue's own five persistent registers. -/
structure Res where
  tLo : Nat
  tHi : Nat
  cel : Nat
  celSq : Nat
  viol : Nat
  deriving Repr, DecidableEq

def readSig (s : AState) : Sig :=
  ⟨s.regs 65, s.regs 79, s.regs 80, s.regs 133⟩

def readRes (s : AState) : Res :=
  ⟨s.regs rTLo, s.regs rTHi, s.regs rCeil, s.regs rCeilSq, s.regs rMViol⟩

/-- (A) `round (2^(63+k) / n)` as a limb pair, from one `2^63` division. -/
def wPair (k n : Nat) : Nat × Nat :=
  let q1 := 2 ^ 63 % M / n % M
  let r1 := 2 ^ 63 % M % n % M
  let a2 := r1 <<< (k % M) % M
  let q2 := a2 / n % M
  let r2 := a2 % n % M
  let q2r := (q2 + (if n ≤ (r2 + r2) % M then 1 else 0)) % M
  let lo0 := q1 <<< (k % M) % M
  let hi0 := q1 >>> ((64 - k) % M) % M
  let wl := (lo0 + q2r) % M
  (wl, (hi0 + (if wl < q2r then 1 else 0)) % M)

/-- (B) `U += μ(n)·w`: a 128-bit add followed by a 128-bit subtract. -/
def accStep (pos neg wl wh tLo tHi : Nat) : Nat × Nat :=
  let b150 := pos * wl % M
  let b151 := pos * wh % M
  let b152 := neg * wl % M
  let b153 := neg * wh % M
  let b154 := (tLo + b150) % M
  let b155 := if b154 < b150 then 1 else 0
  let b157 := ((tHi + b151) % M + b155) % M
  let b158 := if b154 < b152 then 1 else 0
  ((b154 + (M - b152)) % M, ((b157 + (M - b153)) % M + (M - b158)) % M)

/-- (C) `V` biased by `2^63`: `U ≫ (k+1)`, recombined from the two limbs. -/
def vBias (k tLo tHi : Nat) : Nat :=
  ((tLo >>> ((k + 1) % M) % M) ||| (tHi <<< ((63 - k) % M) % M)) % M

/-- (D) `|V|`, branchlessly. -/
def absBias (v : Nat) : Nat :=
  let d153 := if 2 ^ 63 % M ≤ v then 1 else 0
  let d154 := (v + (M - 2 ^ 63 % M)) % M
  let d155 := (2 ^ 63 % M + (M - v)) % M
  let d156 := (1 % M + (M - d153)) % M
  (d153 * d154 % M + d156 * d155 % M) % M

/-- (E) `c = ⌈√(n+1)⌉` and its square, by the increment recurrence. -/
def celStep (n celSq cel gate : Nat) : Nat × Nat :=
  let e161 := (if celSq ≤ n then 1 else 0) * gate % M
  let cel' := (cel + e161) % M
  let e163 := ((cel' + cel') % M + (M - 1 % M)) % M
  (cel', (celSq + e161 * e163 % M) % M)

/-- (F) the test `|V| + ⌈n/2^(k+2)⌉ + 1 ≤ ⌊2^61/c⌋`, counted into `rMViol`. -/
def violStep (k n absV cel gate viol : Nat) : Nat :=
  let f165 := 2 ^ 61 % M / cel % M
  let f167 := (((n + (2 ^ (k + 2) - 1) % M) % M) >>> ((k + 2) % M)) % M
  let f169 := ((absV + f167) % M + 1 % M) % M
  (viol + (if f165 < f169 then 1 else 0) * gate % M) % M

/-- One step of the residue block, as plain `Nat` arithmetic. -/
def resStep (k : Nat) (g : Sig) (r : Res) : Res :=
  let w := wPair k g.n
  let t := accStep g.pos g.neg w.1 w.2 r.tLo r.tHi
  let a := absBias (vBias k t.1 t.2)
  let c := celStep g.n r.celSq r.cel g.gate
  ⟨t.1, t.2, c.1, c.2, violStep k g.n a c.1 g.gate r.viol⟩

/-- The `⌈√(n+1)⌉` register after the step — the divisor of the one `udiv`
in section (F). -/
def celAfter (g : Sig) (r : Res) : Nat :=
  (celStep g.n r.celSq r.cel g.gate).1

end LeanCompCert.Ports.MobiusResidueRealisation
