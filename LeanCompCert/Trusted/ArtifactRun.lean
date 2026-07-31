import LeanCompCert.Trusted.Evidence

/-!
# The admission axiom — opt in, and see it in your `#print axioms`

**Importing this module puts a named axiom in your axiom list.  That is the
point.**  Everything else in `leancompcert` is axiom-free and stays that way:
nothing in the package imports this file, so a consumer who does not ask for
it still gets `[propext, Classical.choice, Quot.sound]` from every certificate.

## What it admits, and what it does not

```lean
abbrev EvidencedRun : Prop :=
  ∀ (p : AProgram) (n : Nat) (e : RunEvidence),
    e.challenge.program = p →
    RunEvidence.verify e n = true →
    p.denote = some n
```

Two premises, and the split matters.  The first says *this record is about this
program*; the kernel discharges it by unfolding the evidence constant and taking
two projections, so it costs the same for every program.  The second is the
record's own coherence, checked by `RunEvidence.verify`.  Both are decidable and
both are re-checked by the kernel; see "Why the program binding is not part of
`verify`" in `LeanCompCert/Trusted/Evidence.lean` for why they are separate —
briefly, real certificate programs are not kernel-reducible to constructor form,
so a `decide (c.program = p)` clause inside `verify` cannot even evaluate.

The conclusion is **`p.denote = some n`, not your mathematics.**  That the
program computes the family you care about — the *encoding gap* — is a
separate obligation and is deliberately not smuggled in here.  Discharge it in
the kernel on a small configuration, or empirically against an independently
written oracle, exactly as
[docs/incorporating-a-computation.md](../../docs/incorporating-a-computation.md)
describes.  An admitted run gives you a number; it does not give you a theorem
about number theory.

Nor does it admit that the compiled C computes the denotation — that is
*proved*, by `AProgram.evalCC_compile`.  What is admitted is the execution:
that a binary really ran and really reported that value.  That is an empirical
fact about a machine and no proof will establish it.

## One statement, one axiom per use site

There are two ways to use this, and they differ in exactly one respect: how
many entries a downstream `#print axioms` shows.

* `evidencedRun_sound` below is the schema exhibited once, as a single named
  axiom.  Using it directly gives **one** entry however many computations you
  admitted, which collapses the audit surface.  It exists so that the
  statement has a name to point at, and for consumers who deliberately want
  the collapsed form.
* The `evidenced_decide` tactic mints a **fresh axiom per use site**, named
  `<declaration>._evidenced.run.ax`, each of type `EvidencedRun`.  This
  mirrors `native_decide`, which since Lean 4.32 emits
  `<declaration>._native.native_decide.ax_1_1` per use rather than a shared
  `Lean.ofReduceBool`.  A reader then gets **one line per admitted execution**,
  greppable and countable, which is the granularity that matters when a
  campaign has 230 shards.

Both are instances of the *same statement*.  An auditor checks the trusted
surface by listing the `._evidenced.run.ax` names and confirming each has type
`EvidencedRun` — one grep and one type check, however many there are.

## What this buys over `native_decide`, honestly

**Better.**  `native_decide` admits Lean's *unverified* compiler and runtime,
opaquely.  This admits CompCert's machine-checked semantic-preservation proof,
plus the assembler and the linker, through a named axiom whose premise is an
**inspectable evidence record** the kernel re-checks.  Strictly smaller and far
better understood.

**Not free.**  The computation has to be expressible in the proved fragment:
no recursion, no early exit, a fixed trip count.  That is real work and it does
not always succeed.  In the consuming ternary-Goldbach project 268
`native_decide` axioms remain, and one measured 220-atom family does *not*
convert by the obvious route — `outward` truncates only at node boundaries
while series and Newton steps build large rationals *inside* a node, so a
whole-way-through fixed-point rewrite is needed first.  Do not present the
replacement as mechanical.

**Same build-time cost.**  Verification is a stamp comparison whose price
depends neither on how long the artifact ran nor on how large the program is;
see the cost note in `LeanCompCert/Trusted/Evidence.lean`.
-/

namespace LeanCompCert.Trusted

open LeanCompCert.Verified.ArrayState

/-- **The one admission schema.**

Every use site gets its own axiom of exactly this type, so the trusted surface
is enumerable by name and uniform in statement.

Read it as: *if a run-evidence record is about program `p`, and it answers the
claim that `p` reports `n`, then `p`'s denotation is `n`.*  Both hypotheses are
decidable and the kernel checks them; the leap is that a passing record
corresponds to a real execution, which is what the axiom asserts and nothing
proves. -/
abbrev EvidencedRun : Prop :=
  ∀ (p : AProgram) (n : Nat) (e : RunEvidence),
    e.challenge.program = p →
    RunEvidence.verify e n = true →
    p.denote = some n

/-- The schema, exhibited once as a named axiom.

Prefer the `evidenced_decide` tactic, which mints one axiom per use site and
so keeps `#print axioms` at the granularity of "one line per admitted
execution".  This constant is here so the statement has a name, and for
callers who deliberately want a single collapsed entry. -/
axiom evidencedRun_sound : EvidencedRun

/-- Convenience wrapper with the arguments in the order a caller usually has
them.  Carries `evidencedRun_sound`, so it collapses the audit surface in the
same way; the tactic is still the recommended path. -/
theorem denote_of_evidence {p : AProgram} {n : Nat} (e : RunEvidence)
    (hp : e.challenge.program = p) (h : RunEvidence.verify e n = true) :
    p.denote = some n :=
  evidencedRun_sound p n e hp h

end LeanCompCert.Trusted
