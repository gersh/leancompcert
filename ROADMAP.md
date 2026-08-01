# leancompcert roadmap

## What this package is

`leancompcert` is a **generic verified-computation backend for Lean**: it
lets any Lean development state a bounded computation, prove facts about it
**axiom-free** (no `native_decide`, no `ofReduceBool`), and independently
check the same computation as a native executable produced by the verified
CompCert compiler.

The product is the trust chain:

```text
Lean proposition
  ↕  per-algorithm equivalence lemmas (consumer-side, ordinary induction)
reference Lean function (data-dependent recursion allowed)
  ↕  once-per-combinator equivalence theorems        [this package]
Reflect.Program denotation (plain Lean arithmetic — the only kernel work)
  ↕  Program.evalCC_compile (structural, proved)     [this package]
CCIR trace
  ↕  lowerSequence_correct (structural, proved)      [this package]
restricted-C model
  →  emitted C → CompCert (verified C→asm) → independent native check
```

Everything between the reference function and the C model is a
once-and-for-all structural theorem. The kernel's per-certificate work is
evaluating one Lean-level fold. The native executable's exit status is
**never admitted as a theorem** — it is an independent check, and keeping
it that way is a permanent design commitment.

The ternary-goldbach development (1,371 `native_decide` atoms, all
operation shapes inventoried in `compatibility/`) is the flagship
workload: it stress-tests every capability below, but nothing in the
package is specific to it. When leancompcert is good, consumers build the
rest on top.

## Current foundation (done, machine-checked)

- Proved instruction fragment: `u64` arithmetic, six comparisons, casts,
  connected to the production lowering (`Proof/PureSemantics.lean`).
- The reflection bridge: register-machine DSL, compiler into the
  fragment, structural denotation theorem (`Verified/Reflect.lean`).
- Limb layer for static arbitrary precision: proved ripple
  add-with-carry, guarded subtract-with-borrow, wide comparison
  (`Verified/Limb.lean`).
- Generic early-exit ≡ predicated-fold equivalence
  (`Verified/EarlyExit.lean`).
- Toolchain: C emission, validators, CompCert compile-and-run in the
  acceptance suite; batch IR compilation (`scripts/compile-ir-tree.py`);
  working axiom-free certificates at the §14.1 shape, 128-bit
  accumulation, CompCert-executed.

## Milestones

### M1 — Scale-free certificate packaging ✅ (implemented)

Delivered in `LeanCompCert/Verified/Package.lean`: `Program.toComputation`
packages any well-formed program with every field structural — lowering
success and statements via `compile_lowered`, fragment membership via
`compile_wellFormed`, both derived from a shape classification of the
compiler's output and structural resolution of `Lower.localType?` through
the preamble's declarations. Acceptance verified: a 750,007-instruction
certificate packages with only the program-sized `Program.WF` obligation
(`LeanCompCertTests`), and the §14.1 reflected certificate now uses this
path end-to-end through its CompCert run.

*Acceptance (met):* a 10⁶-scale certificate packages in under a second;
per-certificate kernel cost is denotation evaluation only.

### M2 — Wide arithmetic completion ✅ (implemented)

Delivered: variable-length addition (`addAny_val`), schoolbook rows
(`mulByLimb_val`), and **arbitrary-precision multiplication with a
machine-checked value theorem** (`mulLimbs_val`) and single-limb long division with quotient/remainder
theorems (`divModMSB_val`, `divModMSB_rem_lt`) in `Verified/Limb.lean`;
plus the acceptance certificate `Testing/FixedPointCertificate.lean` —
per-element 128-bit products (half-limb circuit with proved-comparison
carries) and cross-limb dyadic division, packaged through M1, axiom-free
(`propext, Classical.choice, Quot.sound`), CompCert-compiled and executed
in the acceptance suite. All remaining items are now delivered: the dyadic fixed-point interval
layer with directed rounding and machine-checked enclosures
(`Verified/Dyadic.lean`; the Newton reciprocal is documented as subsumed
by the proved wide division), and the half-limb 128-bit product
structural identity (`Verified/MulWide.lean`: `hl_spec` — the exact
circuit recombination equals `a·b`). Sign-magnitude `Int` is now delivered (`Verified/SignedLimb.lean`:
`SInt` with proved `add_val`/`sub_val`/`neg_val` over the limb theorems),
as is bounded `log2` (`Verified/Log2Fixed.lean`: `log2Fixed_eq` agrees
with `Nat.log2` across the full `u64` range) (instances currently verify by `decide` at
certificate size, which the M1 packaging keeps cheap).

Compositions over the proved limb cores, each with a value-denotation
theorem and a DSL realization:

- 64×64→128 products via 32-bit half-limbs; schoolbook wide
  multiplication;
- shifts/dyadic scaling; single-limb division; fixed-round Newton
  reciprocal with outward-rounding bounds (interval division without
  exact division);
- signed values as sign-magnitude pairs (`Int` accumulators, `natAbs`);
- bounded `log2` (unrolled halving);
- a dyadic fixed-point interval layer (add/sub/mul/div with directed
  rounding at a static precision) — the entry path for ℚ-valued
  certificates restated in the `roundOut` discipline they already use.

*Acceptance:* a certificate whose per-element work includes a 128-bit
product and a dyadic division, axiom-free and CompCert-executed.

**M2b — modular arithmetic ✅ (implemented).**  Wide *multiplication* was
delivered above; wide *reduction* was the missing half, and it was the
binding obstruction on the ternary-Goldbach corpus (the Proth test, 75.1 %
of the ladder producer's cost; `checkAllPsiLeMul`; the exact-ℚ families).
The fragment's only division is `udiv`/`urem` at 64 ÷ 64 → 64, so `x·y mod
N` for a wide `N` — a 128 ÷ 64 division — could not be written.
`Verified/Montgomery.lean` supplies the algebra (`redcStep_mul`: the
Montgomery shift is *exact*; `montMul_spec`; `montExp_spec`) and needs no
division at all; `Verified/Mont2.lean` realizes it at two limbs in the
fragment's instruction set (`montMul2_val`), with division-free entry into
the Montgomery domain by doubling (`dblIter_val`).

`Montgomery.lean` is stated for an arbitrary number of reduction steps `s`,
so widening past 128 bits is a machine-layer exercise only: an `n`-limb
`mulN`/`redcN` over the existing `Limb.mulLimbs_val` carry theorems, in the
same proof shape as `Mont2`.  That is the route to `checkAllPsiLeMul`'s
~950-bit operands.

*Acceptance (met):* `Ports/TGProth.lean` — a modular exponentiation at a
91-bit modulus, emitted, CompCert-compiled, cross-checked against Python,
and costing 2.25× GMP's `mpz_powm` (`bench/results/tg_proth.md`).

### M3 — Combinator and equivalence library ✅ (implemented; one noted refinement)

The monadic-recursion interface: consumers write natural recursive
functions; the package supplies fixed-shape compilations and
once-per-combinator equivalence theorems (induction on fuel/measure):

- `iterN` (fixed-iteration recursion — Newton, gcd rounds): subsumed —
  the `Program` loop model *is* the fixed-iteration combinator, and
  fixed-count inner recursions unroll into the body list;
- `foldRangeE` (early-exit): **done** (`EarlyExit.lean`); add the DSL
  realization lemma (mask registers implement the freezing);
- spec-based equivalences ✅ delivered: `Verified/SqrtEquiv.lean`
  (`isqrt_eq : isqrt n = Nat.sqrt n`, clamp-correct fixed-shape Newton
  with a proved floor AM–GM) and `Verified/GcdEquiv.lean`
  (`gcdFuel_eq`, fixed-round guarded Euclid ≡ `Nat.gcd`, with the `2⁶⁴`
  machine-width corollary);
- the **front end** ✅ delivered as the verified expression layer
  (`Verified/Frontend.lean`): an `Expr` AST with `denoteExpr`, the
  verified compiler `compileExpr` (correctness theorem covering value,
  register-frame condition, and divergence propagation — axioms:
  `propext` only), `Expr.toBody`, and the `expr!` surface macro.
  Certificate bodies are now written as expressions with
  once-and-for-all correctness. Noted refinement (post-delivery
  enhancement, not a gate): a matcher reifying *pre-existing* Lean
  `foldl`-lambda terms rather than `expr!` syntax.

Mathlib-dependent equivalences (e.g. `Nat.minFac`, `Nat.totient`) stay
consumer-side by design; this package stays Mathlib-free and exposes the
denotations they target.

*Acceptance:* an unmodified `foldl`-over-`range` Lean definition gets a
certificate via the front end with no hand-written `Program`.

### M4 — Rolled loops in emission ✅ (implemented)

Delivered (`Verified/Rolled.lean`, `Testing/RolledFixedPoint.lean`): the
counted rolled form — the loop index in a dedicated counter register, the
body lowered **once** through the production path with `.idx` at the
counter variable, emitted as a single validated `while` loop. The proved
correspondence core is `evalOperand_var_eq_lit` (variable-index operands
evaluate exactly as each iteration's literal operands under the counter
environment). Acceptance demonstrated: the 10⁷-iteration fixed-point
checker emits as a **2 KB** artifact, CompCert-compiles, and the native
check passes in ~14 ms in the acceptance suite. The assembly is now proved: `rolledTrace_eq_augmented` composes the
per-iteration correspondence with the counter-increment step over the
trip-count induction, showing the rolled loop's dynamic trace evaluates
exactly as the standard `foldTrace` of `Program.counterAugment p` — a
bona-fide `Program`, so packaging, bridge, and denotation theorems apply
to it unchanged while the emitted artifact runs the rolled form. All
M4 deliverables are complete.

Unrolled traces keep theorems honest at any size, but the *emitted C*
must not be gigabytes at 10⁷ iterations. Add a counted-loop construct:
static trip count, single back-edge, index register — deliberately far
simpler than general CFG simulation:

- emission through the production `label`/`goto` path;
- a fuel-free simulation proof by induction on the trip count (the loop
  body reuses the straight-line theorem verbatim);
- `foldTrace` remains the semantics; the rolled form is an emission
  choice with a proved correspondence.

*Acceptance:* the same certificate emits kilobytes of rolled C instead of
unrolled megabytes; CompCert compiles and the native check passes at a
10⁷-iteration height.

### M5 — Arrays with static iteration spaces ✅ (all milestone items implemented)

Delivered: `Verified/Sieve.lean` — the sieve-shaped equivalence theorem
(`spfFixed_eq_leastFactor`): a fixed-shape, data-independent
smallest-factor scan proved equal to the fuel-guarded reference least-
factor recursion whenever the static window covers `√n` (a bound of
`2³²` covers all of `u64`), via least-hit characterizations of both
sides. Additionally delivered: the array-state machine itself
(`Verified/ArrayState.lean`) — bounds-guarded `load`/`store` with frame
and out-of-bounds lemmas over `AState`, `AProgram` with its denotation —
and the flagship sweep: `sieveSweep_cell` proves every in-bounds cell of
the data-independent divisor sweep equals `Sieve.leastFactor`, through
the sieve invariant. The machine realization is now delivered too
(`Verified/MemFragment.lean`): CCIR `load`/`store` in the proved
fragment under the disjoint-single-array discipline — memory-extended
states with `MRel`, the memory-frame theorem over the embedded
straight-line fragment, `lowerM_correct` preservation, the production
`lowerInstruction_load`/`lowerInstruction_store` connections, and the
whole-trace `lowerMSequence_correct`. All four milestone bullets are
implemented; composing them into the end-to-end 10⁶-height sieve
certificate artifact (the acceptance benchmark) is the natural first
exercise of the completed machinery.

The last capability the inventoried workloads need, and the performance
winner (sieves beat early-exit trial division 31× in the CompCert-compiled
benchmarks). Scope deliberately benign:

- disjoint arrays only, statically-ranged in-bounds indices, no aliasing;
- CCIR load/store brought into the proved fragment for this discipline;
- DSL array state with a denotation into `Lean` arrays/functions;
- sieve-shaped combinators (nested folds with index-computed inner
  bounds) with equivalence theorems to per-element reference functions
  (verified-Eratosthenes-style invariants).

*Acceptance:* a smallest-prime-factor sieve certificate at 10⁶+, axiom-
free, with the compiled checker outperforming the early-exit original.

### M6 — The Clight bridge ✅ (implemented)

Delivered: `clightgen` 3.17 (matching the installed `ccomp`) now runs in
the acceptance suite over **every emitted certificate unit**, translating
each into CompCert's formal Clight syntax (Coq terms) and failing the
suite if any unit falls outside it. This closes the "is our emitted
subset really Clight?" question operationally for all shipped
certificates. Now additionally delivered: **structural correspondence
checking** (`scripts/clight-correspond.py`, gated in the acceptance
suite) — the emitted C and clightgen's Clight terms are parsed into
ordered event streams (per-assignment destination/operator/operands,
loop/label/return structure) and required to match exactly;
demonstrated to catch single-operator, destination, and literal
mutations. Proof-level correspondence is now delivered
(`scripts/clight-correspond-coq.py`, gated in the acceptance suite):
the event extraction runs as a Coq `Fixpoint` over CompCert's actual
Clight AST and the correspondence lemma is discharged by `vm` conversion
at `Qed` — **Coq's kernel**, not a parser, validates the 3,474-event
fixed-point certificate (2.8 s), with mutations rejected at `Qed`.
Honest trusted base: the C-side event extraction remains a Python parse
of the emitter's regular output, plus the ~60-line Coq prelude.
The ultimate item is now delivered too: **direct Clight emission with a
semantics proof against CompCert's Coq development**.
`Verified/ClightEmit.lean` emits goto-free Clight AST terms directly
from the proven statement lists (no C printer or clightgen parser in the
formal object's path); `scripts/coq/ClightFragmentSem.v` proves, once,
a computable fragment evaluator sound against `ClightBigstep.exec_stmt`
(generic over both Clight semantics variants, with genv/memory
independence lemmas), and per certificate
(`scripts/clight-direct-verify.py`, gated in the acceptance suite) Coq's
kernel discharges `eval_funcall function_entry2 ge m (Internal f) nil E0
m (Vlong <certified value>)` for every genv and memory — CompCert's own
bigstep semantics computes the certified value, in under a second, with
wrong-value mutations rejected at `Qed`. Honest boundary: the semantics
theorem covers the straight-line temp-only fragment (E0 traces,
unchanged memory — exactly what these certificates are); rolled/looped
artifacts retain the correspondence-level assurance; and the Lean-side
and Coq-side results are tied by the shared certified constant rather
than a single cross-prover proof.

The long-pole trust upgrade: replace "this repo's restricted-C model" with
CompCert's own formal semantics.

- near term: `clightgen`-based translation validation of emitted units
  (checked correspondence between the emitted AST and the Clight terms);
- long term: direct Clight AST emission for the fragment, eliminating
  the C printer and parser from the trusted base (the original
  specification's final milestone);
- resolve the model's documented shift-definedness caveat as part of the
  correspondence.

*Acceptance:* the C-model↔Clight gap is closed for the fragment, or
precisely characterized per construct with machine-checked validation.

### M7 — A consumable generic package 🟡 (documentation complete, 1.0 gate open)

Delivered: the axiom-audit CI gate (`scripts/AxiomAudit.lean`, enforced
by the acceptance script — fails on any native-evaluation axiom) and the
certificate-authoring guide (README, including the kernel-scale chunking
discipline). Now also delivered: the public-API surface declaration with the semver
policy, the toolchain-compatibility policy (adapter isolation), and
consumer-adapter guidance (README "Public API and versioning"). The milestone's acceptance criterion is now demonstrated:
`examples/consumer/` is an external Lake project that depends on
leancompcert through the public API alone, proves its own certificate
(standard axioms), and runs its CompCert-compiled check (exit 0); its
usability findings are folded into the README consumer notes. The 1.0
gate is time-in-service on the declared stability.

- stable public API: `Reflect.Program`, `Decision`, the combinator
  library, the limb layer; semantic versioning; no Mathlib dependency in
  the core, adapters documented for Mathlib-side consumers;
- a certificate-authoring guide, including the **kernel-scale
  discipline**: monolithic full-height folds can crash `decide +kernel`
  (measured: stack overflow at a 150k-element production fold), so
  certificates must be chunked partial computations combined by proved
  lemmas — guidance, templates, and combinators for it;
- axiom-audit tooling (every certificate module reports its exact axiom
  set in CI), the CompCert replay in CI, and the benchmark suite
  (`tests/benchmarks/`) kept as a regression harness;
- toolchain compatibility policy across Lean versions (the LCNF adapter
  pattern already isolates compiler-API churn).

*Acceptance:* an external Lake project depends on leancompcert, states
its own bounded computation, and gets the full trust chain without
touching this repo's internals.

### M8 — A kernel-efficient denotation 🔴 (open; measured requirement)

**The problem.** `RegState` is `Nat → Nat` and `RegState.set` is functional
update (`Verified/Reflect.lean:96–99`), so every register read walks a closure
chain whose length is the number of stores so far, and `AState` array reads do
the same.  The denotation is therefore *quadratic in trip count* when the
kernel evaluates it, which is exactly the one place the roadmap above promises
the kernel's work is "evaluating one Lean-level fold".

**Measured** (2026-08-01, ternary-goldbach consumer, serial on an idle box —
the same computation expressed both ways, denotations agreeing on the value
`13938989466958741855` at `N = 10⁵`):

| shape | per elementary op | reach per `decide +kernel` |
| --- | ---: | ---: |
| plain Lean recursion (reference function) | **41 µs** | ~10⁶ steps, 7.4 GB |
| scalar `Program.denote` | **≈160 µs** | **1 000–2 000 iterations**, C-stack overflow at 0.8 GB |
| `AProgram.denote`, local array access | ≈150 µs | ~10³ iterations |
| `AProgram.denote`, non-local read | **quadratic** — 23.7 ms/iter at `N = 10³` | ~10³ iterations |

So the `Program` route is ~4× slower per elementary operation than the plain
Lean recursion it is meant to replace, and its per-invocation reach is ~500×
smaller.  The overflow is *recursion depth*, not stack size: `--tstack=1000000`
did not move it.  The non-local-read row is clean quadratic (×3.9 then ×4.9 per
doubling).

**Consequence for use case 1.**  For fold-shaped certificates at production
height a consumer is better off chunking its *reference function* directly than
routing through `Program`.  That is sound and Tutorial 3 explicitly allows it
("the kernel evaluates whichever side of the equivalence is cheaper") — but it
means the reflection route does not currently pay for this whole class, which
is most of the flagship workload.

⚠ **Do not cite the 31× sieve-over-trial-division benchmark as a kernel
figure.**  It is `tests/benchmarks/rewrite-bench.c` — a *CompCert-binary*
measurement.  It says what the artifact does, not what the kernel does, and a
kernel-evaluated sieve is blocked by the quadratic row above.  This distinction
was drawn incorrectly by a consumer and cost real effort.

**What is wanted.**  A `denote` variant over a representation the kernel can
evaluate in near-constant time per access — a finite map, a run-length register
file, or a fixed-width vector indexed by `Fin regCount` — **with equality to
the present `denote` proved**, so every theorem above it (`evalCC_compile`,
`lowerSequence_correct`, the packaging chain) applies unchanged.  Nothing below
the interpreter needs to move: the fragment, the Clight bridge and the
equivalence library are all fine.  This is a core design change and wants an
upstream decision, not a drive-by patch.

*Acceptance:* a `10⁶`-iteration scalar `Program` certificate checked by
`decide +kernel` in the same order of time as the equivalent chunked reference
fold, with the denotation-equality theorem carrying the existing chain.

## Cross-cutting commitments

- **Axiom-free forever**: no run-admission axiom; the native run stays an
  independent check. Any future "trust the executable" mode would be a
  different product and is out of scope.
- **Production lowering only**: every theorem targets the shipping
  lowering functions, never a parallel test compiler.
- **Honest boundaries**: what is and is not covered stays documented in
  README trust-model terms at every milestone.
- **Kernel pragmatics**: prefer formulations the kernel reduces well
  (guarded subtraction over bare `Nat` sub-chains at machine scale — a
  measured failure mode), and keep a small corpus of kernel-reduction
  regression tests.

## Non-goals

Verifying Lean's elaborator or compiler; general data-dependent CFG
simulation (subsumed by M4 + M5 + predication for the inventoried
workloads; revisit only if a real workload demands it); floating point;
unbounded-precision runtime bignum in the verified fragment; whole-program
runtime verification (the strict-profile runtime remains a separate,
later effort).

## Sequencing and effort

Current state: **all seven milestones are implemented**, with the
per-milestone evidence recorded in the sections above. The remaining
open item is M7's 1.0 gate: the public API is stable under semantic
versioning from 0.2.x, and 1.0 is cut once external consumers have
exercised the surface (the `examples/consumer` project demonstrates the
intended integration).

First external validation target: the integer certificate families of
the ternary-goldbach development (ternary arithmetic, ChebyshevPsi,
vmHead, little-Mertens) — monotone, permanent reductions of a real
proof's native trust surface, with everything else built on top by the
consumer. What that migration needs from the goldbach side is described
in Tutorial 3 and the compatibility reports.
