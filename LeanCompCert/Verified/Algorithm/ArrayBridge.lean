import LeanCompCert.Verified.Algorithm.Spec
import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.ArrayBridge

/-!
# `ArrayBridge` — the array refinement combinator

`docs/algorithm-to-proof.md` §3 lists the combinators that prove the
`ProgramRefinement` obligation and names `ArrayBridge` among them.  Two
different things were missing behind that name, and this module supplies the
second of them:

* `Verified/ArrayBridge.lean` is the **compiler** bridge for the array
  machine — `AProgram.compile`, `AProgram.evalCC_compile`,
  `AProgram.evalC_compile`.  It relates a program to the C it becomes.  It
  already existed.
* `Verified/ArrayFoldBridge.lean` is the **reasoning** bridge — the array
  analogue of `Verified/FoldBridge.lean`, turning `AProgram.denote` into a
  `List.foldl` written in ordinary mathematics.
* This module is the **refinement** bridge: it packages the two into the
  `Algorithm`/`ProgramRefinement` shape, so an array port discharges the same
  audit checklist as a scalar one.

## Why the array machine needs its own `ProgramRefinement`

`Algorithm.ProgramRefinement` is stated over `Reflect.Program`, whose
denotation has an `iff` all the way to a `Computation.Returns`.  An array
program is a different type (`AProgram`) with a different denotation
(`AProgram.denote`, over `AState`), and — importantly — its compiler bridge is
**one-way**: `AProgram.evalCC_compile` says

```text
  p.denote = some n  →  (compiled trace).output = some n
```

and not the converse, because `u64` address arithmetic makes the cell map
non-injective over the whole register range (see `Verified/ArrayBridge.lean`).
So `AProgramClaim` below deliberately has no `Computation.Returns` iff.  What
it has instead is `trace_value_unique`: a *proved* denotation plus an observed
run value forces the two to agree.  A run therefore **reads off** an array
program's denotation; it never establishes one.  That asymmetry is real and is
recorded here rather than papered over.

## The two obligations, unchanged

The split of `docs/algorithm-to-proof.md` is preserved exactly:

```text
reference algorithm succeeds          →  mathematical proposition
                                                        Algorithm.Ensures
array program returns a decodable result →  reference algorithm succeeds
                                                        AProgramRefinement
```

`ArrayLoop` is the data of the second arrow's proof: a loop invariant, a step,
an observation, and the four simulation obligations of
`ArrayFoldBridge.AProgram.denote_eq_obs_foldl_mem` — each of them
`∀`-quantified over states, hence size-independent.

## Side conditions are part of the decoder, not a footnote

Every real array port's denotation holds only under arithmetic side
conditions: no index wraps modulo `2⁶⁴`, the array is long enough, a divisor
is nonzero.  `AProgramRefinement.ofDenotationOn` takes those as an explicit
`Admissible` predicate and *requires* (`decode_admissible`) that the decoder
reject every input for which they are not known to hold.  A port therefore
cannot state its side conditions in a docstring and forget them in the
certificate: the audit item "`decode` rejects every non-accepting machine
result" is extended to "and every inadmissible input".
-/

namespace LeanCompCert.Verified.Algorithm

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

universe u v w

/-! ## The loop package -/

/--
**An array loop with its simulation proof.**

The bundled form of `ArrayFoldBridge.AProgram.denote_eq_obs_foldl_mem`: an
abstract observation `obs` of the machine state, folded by `g`, read out by
`out`, with an invariant `inv` that the body preserves.

Each obligation is quantified over all states and restricted to the indices
the loop actually visits (`index < program.loopCount`).  The restriction is
load-bearing rather than convenient — a body that decodes a divisor or an
array offset from the loop index is genuinely undefined at an adversarial
index, so the unrestricted `FoldBridge` shape is unprovable for it.
-/
structure ArrayLoop (A : Type u) where
  /-- The array program whose denotation is being characterized. -/
  program : AProgram
  /-- The loop invariant. -/
  inv : AState → Prop
  /-- The machine step, as a total state function. -/
  step : Nat → AState → AState
  /-- What the loop carries between iterations, in mathematics. -/
  obs : AState → A
  /-- The mathematical step on the observation. -/
  g : Nat → A → A
  /-- How the epilogue reads the answer out of the observation. -/
  out : A → Nat
  /-- The state the initialization block reaches. -/
  entry : AState
  init_reaches :
    denoteAInstrs program.arrayLen 0 initialAState program.init = some entry
  inv_entry : inv entry
  body_sim : ∀ index s, index < program.loopCount → inv s →
    denoteAInstrs program.arrayLen index s program.body = some (step index s)
  inv_step : ∀ index s, index < program.loopCount → inv s → inv (step index s)
  obs_step : ∀ index s, index < program.loopCount → inv s →
    obs (step index s) = g index (obs s)
  epilogue_reads : ∀ s, inv s →
    (denoteAInstrs program.arrayLen 0 s program.epilogue).map
      (fun s' => s'.regs program.output) = some (out (obs s))

namespace ArrayLoop

variable {A : Type u}

/-- The value the loop computes, as a fold in ordinary mathematics.  No
register, no trace and no problem size appears in it. -/
def value (loop : ArrayLoop A) : Nat :=
  loop.out ((List.range loop.program.loopCount).foldl
    (fun acc index => loop.g index acc) (loop.obs loop.entry))

/-- **The bridge, packaged.**  The program denotes the fold. -/
theorem denote (loop : ArrayLoop A) : loop.program.denote = some loop.value :=
  AProgram.denote_eq_obs_foldl_mem loop.program loop.inv loop.step loop.obs
    loop.g loop.out loop.entry loop.init_reaches loop.inv_entry loop.body_sim
    loop.inv_step loop.obs_step loop.epilogue_reads

/-- Rewriting the folded value: a port proves its own closed form and quotes
this to get the denotation. -/
theorem denote_eq (loop : ArrayLoop A) {n : Nat} (h : loop.value = n) :
    loop.program.denote = some n := by
  rw [loop.denote, h]

end ArrayLoop

/-! ## The refinement obligation, for array programs -/

/--
A proved one-way refinement from an **array** register program to a reference
algorithm — the `AProgram` analogue of `ProgramRefinement`.

As there, the refinement theorem is conditional on successful decoding: only
results the decoder accepts have to refine a successful reference run.
-/
structure AProgramRefinement {Input : Type u} {Output : Type v}
    (algorithm : Algorithm Input Output) where
  program : Input → AProgram
  wellFormed : ∀ input, (program input).WF
  decode : Input → Nat → Option Output
  refines : ∀ input value output,
    (program input).denote = some value →
    decode input value = some output →
    algorithm.run input = some output

namespace AProgramRefinement

variable {Input : Type u} {Output : Type v} {algorithm : Algorithm Input Output}

/-- A decoded successful array-program result is a successful reference
result. -/
theorem source_succeeds (refinement : AProgramRefinement algorithm)
    {input : Input} {value : Nat} {output : Output}
    (returned : (refinement.program input).denote = some value)
    (decoded : refinement.decode input value = some output) :
    algorithm.run input = some output :=
  refinement.refines input value output returned decoded

/--
**`ArrayBridge` — the combinator.**

Build the refinement from a proved family denotation.  `Admissible` carries
the arithmetic side conditions under which the denotation was proved, and
`decode_admissible` forces the decoder to reject inadmissible inputs, so the
side conditions are visible in the certificate rather than only in a proof.

`decode_sound` is the remaining obligation and is the one that mentions the
reference algorithm: when the input is admissible and the decoder accepts the
denoted value, the reference algorithm succeeds with the decoded output.
-/
def ofDenotationOn (algorithm : Algorithm Input Output)
    (program : Input → AProgram)
    (wellFormed : ∀ input, (program input).WF)
    (Admissible : Input → Prop)
    (value : Input → Nat)
    (denotes : ∀ input, Admissible input → (program input).denote = some (value input))
    (decode : Input → Nat → Option Output)
    (decode_admissible : ∀ input result output,
      decode input result = some output → Admissible input)
    (decode_sound : ∀ input output, Admissible input →
      decode input (value input) = some output → algorithm.run input = some output) :
    AProgramRefinement algorithm := {
  program
  wellFormed
  decode
  refines := by
    intro input result output returned decoded
    have hadm : Admissible input := decode_admissible input result output decoded
    have hval : result = value input := by
      have := (denotes input hadm).symm.trans returned
      exact (Option.some_inj.mp this).symm
    subst hval
    exact decode_sound input output hadm decoded
}

/--
The unconditional specialization: a family whose denotation is proved for
every input, with the decoder testing the machine result against a claimed
accepting value.  This is the shape a shard certificate uses — the claimed
value is part of the input, so `Algorithm.Ensures` can talk about it.
-/
def ofDenotation (algorithm : Algorithm Input Output)
    (program : Input → AProgram)
    (wellFormed : ∀ input, (program input).WF)
    (value : Input → Nat)
    (denotes : ∀ input, (program input).denote = some (value input))
    (decode : Input → Nat → Option Output)
    (decode_sound : ∀ input output,
      decode input (value input) = some output → algorithm.run input = some output) :
    AProgramRefinement algorithm :=
  ofDenotationOn algorithm program wellFormed (fun _ => True) value
    (fun input _ => denotes input) decode (fun _ _ _ _ => trivial)
    (fun input output _ h => decode_sound input output h)

/--
**The loop form.**  The combinator most array ports will use: supply an
`ArrayLoop` per input together with the closed form of its fold, and the
refinement follows.  `ArrayLoop`'s fields are exactly the size-independent
simulation obligations; nothing here evaluates a loop.
-/
def ofArrayLoopOn {A : Type w} (algorithm : Algorithm Input Output)
    (loop : Input → ArrayLoop A)
    (wellFormed : ∀ input, (loop input).program.WF)
    (Admissible : Input → Prop)
    (value : Input → Nat)
    (closedForm : ∀ input, Admissible input → (loop input).value = value input)
    (decode : Input → Nat → Option Output)
    (decode_admissible : ∀ input result output,
      decode input result = some output → Admissible input)
    (decode_sound : ∀ input output, Admissible input →
      decode input (value input) = some output → algorithm.run input = some output) :
    AProgramRefinement algorithm :=
  ofDenotationOn algorithm (fun input => (loop input).program) wellFormed
    Admissible value
    (fun input hadm => (loop input).denote_eq (closedForm input hadm))
    decode decode_admissible decode_sound

end AProgramRefinement

/-! ## Packaging -/

/-- A reference algorithm, its mathematical soundness proof, and its verified
array compilation packaged as one object — the `AProgram` analogue of
`CertifiedAlgorithm`. -/
structure ACertifiedAlgorithm (Input : Type u) (Output : Type v)
    (proposition : Input → Prop) where
  algorithm : Algorithm Input Output
  sound : algorithm.Ensures proposition
  compilation : AProgramRefinement algorithm

/--
A closed compiled claim about an array program.

Unlike `ProgramClaim` this carries **no** `Computation.Returns` bridge: the
array compiler bridge is one-way (see the module docstring), so acceptance of
a physical run cannot by itself establish `program.denote = some value`.  Use
`AProgramClaim.trace_value_unique` instead: prove the denotation structurally,
then let the run read the number off it.
-/
structure AProgramClaim (proposition : Prop) where
  program : AProgram
  wellFormed : program.WF
  acceptingValue : Nat
  sound : program.denote = some acceptingValue → proposition

namespace ACertifiedAlgorithm

variable {Input : Type u} {Output : Type v} {proposition : Input → Prop}

/-- Specialize a certified array algorithm to one closed input and one decoded
accepting result. -/
def claim (certified : ACertifiedAlgorithm Input Output proposition)
    (input : Input) (acceptingValue : Nat) (output : Output)
    (decoded : certified.compilation.decode input acceptingValue = some output) :
    AProgramClaim (proposition input) := {
  program := certified.compilation.program input
  wellFormed := certified.compilation.wellFormed input
  acceptingValue
  sound := by
    intro returned
    exact certified.sound input output
      (certified.compilation.refines input acceptingValue output returned decoded)
}

end ACertifiedAlgorithm

/-! ## What a physical run of an array program can and cannot do -/

/--
**The honest run rule for array programs.**

Given a *proved* denotation `p.denote = some n` and a run of the compiled CCIR
trace that produced `v`, the two agree.  The proof is `evalCC_compile` plus
injectivity of `some`: the trace is a function of the program, so it cannot
produce two values.

This is the array counterpart of `ProgramClaim.prove`, and it is weaker in
exactly one respect: `n` must already be known.  A run reads a proved
denotation off; it does not establish one.  Strengthening this to the scalar
`iff` needs either abstract pointer arithmetic in CCIR or an explicit
out-of-range trap in the emitted code, both of which are fragment-extension
decisions taken nowhere in this package.
-/
theorem trace_value_unique (p : AProgram) (hWF : p.WF) (base : Int)
    (hBase : BaseOk p.arrayLen base) (n v : Nat)
    (hDenote : p.denote = some n)
    (hRun :
      Option.bind
        (Verified.MemFragment.evalMCCSequence (p.initialMCC base) p.compile)
        (fun m : Verified.MemFragment.MCCState => m.env ⟨p.output + 1⟩) =
      some ((v : Nat) : Int)) :
    v = n := by
  have htrace := AProgram.evalCC_compile p hWF base hBase n hDenote
  rw [hRun] at htrace
  exact Int.ofNat_inj.mp (Option.some_inj.mp htrace)

/-- The same statement for a packaged claim. -/
theorem AProgramClaim.trace_value_unique {proposition : Prop}
    (claim : AProgramClaim proposition) (base : Int)
    (hBase : BaseOk claim.program.arrayLen base) (v : Nat)
    (hDenote : claim.program.denote = some claim.acceptingValue)
    (hRun :
      Option.bind
        (Verified.MemFragment.evalMCCSequence
          (claim.program.initialMCC base) claim.program.compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨claim.program.output + 1⟩) =
      some ((v : Nat) : Int)) :
    v = claim.acceptingValue :=
  _root_.LeanCompCert.Verified.Algorithm.trace_value_unique claim.program
    claim.wellFormed base hBase claim.acceptingValue v hDenote hRun

end LeanCompCert.Verified.Algorithm
