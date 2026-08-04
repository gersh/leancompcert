import LeanCompCert.Ports.CeDyadicFold
import LeanCompCert.Verified.Algorithm.Spec

/-!
# The dyadic prime-fold as a `ProgramClaim`

`Ports/CeDyadicFold.lean` proves what the register program denotes.  This
module packages that into the single implication a consumer needs, and states
the per-candidate term `ceTerm` in the shape the consumer's own certificate
term already has, so that the two can be identified by `rfl`.

## What this does and does not establish

`ProgramClaim.prove` takes a `Computation.Returns` hypothesis.  This module
neither creates nor admits one.  Everything below is an ordinary Lean theorem
about `Program.denote`; nothing here asserts that any physical execution
happened, and nothing here adds an axiom.

⚠ `CeDyadicFold.ceRun_spec` is still open (`sorry`), so `ceProgram_denote` and
therefore `ceClaim.sound` are **not** yet proved from the base trio.  Nothing
below states an axiom to paper over that.
-/

namespace LeanCompCert.Ports.CeDyadicClaim

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.Algorithm
open LeanCompCert.Ports.CeDyadicFold

/-!
## The per-candidate term

`ceTerm c n k` is the plain-`Nat` value one block of `R` rounds accumulates for
the candidate `n` carrying the dyadic exponent `k`.  It is written so that at
`c.up = 0` it reduces to the consumer's lower (max) term and at `c.up = 1` to
the consumer's upper (min) term, by `rfl` once `c` is a concrete instance.
-/
def ceTerm (c : Params) (n k : Nat) : Nat :=
  if c.up = 1 then
    let pk := 2 ^ k
    let C := n * (n - 1)
    let sA := sd (2 * pk * n) (n * n - pk * pk)
    let FA := sA.1 + (if sA.2 = 0 then 0 else 1)
    let FB := (sd (4 * pk * pk + 8 * pk * n + n * n)
      (3 * (4 * pk * pk - n * n))).1
    let q0 := c.lfx / C
    let r0 := c.lfx % C
    let tA := k * q0 + (k * r0 + FA + C - 1) / C
    let a1 := (k + 1) * r0
    let base := (k + 1) * q0
    let fB := (FB - a1) / C
    let tB := if a1 ≤ FB then (if fB ≤ base then base - fB else tA)
              else base + (a1 - FB + C - 1) / C
    min tA tB
  else
    let pk := 2 ^ k
    let C := n * (n - 1)
    let FA := (sd (n * n + 4 * n * pk + pk * pk) (3 * (n * n - pk * pk))).1
    let sB := sd (4 * pk * n) (4 * pk * pk - n * n)
    let FB := sB.1 + (if sB.2 = 0 then 0 else 1)
    let q0 := c.lfx / C
    let r0 := c.lfx % C
    let tA := k * q0 + (k * r0 + FA) / C
    let a1 := (k + 1) * r0
    let base := (k + 1) * q0
    let fB := (FB - a1 + C - 1) / C
    let tB := if a1 ≤ FB then (if fB ≤ base then base - fB else tA)
              else base + (a1 - FB) / C
    max tA tB

/-- The trial divisor of round `r`: `2`, then the odd numbers from `3`. -/
def tdiv (r : Nat) : Nat := if r = 0 then 2 else 2 * r + 1

/-- The final state of the flat fold. -/
def ceFinal (c : Params) : Vals :=
  (List.range (c.len * c.R)).foldl (fun v k => ceRound c k v) (initVals c)

/-- The proposition the program certifies, in plain `Nat`. -/
def ceAccepts (c : Params) : Prop :=
  (ceFinal c).ok = 1 ∧
    (if c.up = 1 then (ceFinal c).acc ≤ c.bound else c.bound ≤ (ceFinal c).acc)

/--
**The consumer's entry point.**

If the compiled program returns the accepting value `1`, then the flat fold
reached the certified side of `bound` without any accumulator step wrapping.

Both halves are one-way, as they should be: a program that returned `0` would
say nothing, which is exactly what a certificate is entitled to.
-/
theorem ceAccepts_of_denote (c : Params) (hP : c.Sane)
    (hrun : (ceProgram c).denote = some 1) : ceAccepts c := by
  rw [ceProgram_denote c hP] at hrun
  have hval : (if ((List.range (c.len * c.R)).foldl
        (fun v k => ceRound c k v) (initVals c)).ok = 1 ∧
      (if c.up = 1
        then ((List.range (c.len * c.R)).foldl
                (fun v k => ceRound c k v) (initVals c)).acc ≤ c.bound
        else c.bound ≤ ((List.range (c.len * c.R)).foldl
                (fun v k => ceRound c k v) (initVals c)).acc)
      then 1 else 0) = 1 := Option.some.inj hrun
  by_cases hc : ceAccepts c
  · exact hc
  · have hc' : ¬ (((List.range (c.len * c.R)).foldl
          (fun v k => ceRound c k v) (initVals c)).ok = 1 ∧
        (if c.up = 1
          then ((List.range (c.len * c.R)).foldl
                  (fun v k => ceRound c k v) (initVals c)).acc ≤ c.bound
          else c.bound ≤ ((List.range (c.len * c.R)).foldl
                  (fun v k => ceRound c k v) (initVals c)).acc)) := hc
    rw [if_neg hc'] at hval
    exact absurd hval (by omega)

/-- The claim, ready for any independent provider of a `Computation.Returns`
fact — the kernel for a small instance, a local runner, or an attested remote
run.  This library depends on none of them. -/
def ceClaim (c : Params) (hP : c.Sane) : ProgramClaim (ceAccepts c) := {
  program := ceProgram c
  wellFormed := ceProgram_wf c
  acceptingValue := 1
  sound := ceAccepts_of_denote c hP
}

@[simp] theorem ceClaim_program (c : Params) (hP : c.Sane) :
    (ceClaim c hP).program = ceProgram c := rfl

@[simp] theorem ceClaim_acceptingValue (c : Params) (hP : c.Sane) :
    (ceClaim c hP).acceptingValue = 1 := rfl

/-! ## The two instances -/

/-- The lower (floor / max) instance: primes in `[20001, 25000000]`. -/
def cfgCe : Params :=
  ⟨20001, 24980000, 2501, 14, 0, 12786308640407511063, 920304943318662⟩

/-- The upper (ceiling / min) instance: primes in `[20001, 200000]`. -/
def cfgCeU : Params :=
  ⟨20001, 180000, 2501, 14, 1, 12786308649630883101, 828905072852048⟩

theorem cfgCe_sane : cfgCe.Sane :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

theorem cfgCeU_sane : cfgCeU.Sane :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

example : cfgCe.lo + cfgCe.len - 1 = 25000000 := by decide
example : cfgCeU.lo + cfgCeU.len - 1 = 200000 := by decide

end LeanCompCert.Ports.CeDyadicClaim
