# Tutorial 5 — Loops, arrays, and large-scale certificates

> **Vocabulary.** *Denotation* means what a program computes as ordinary
> Lean arithmetic, defined mathematically rather than by running anything;
> *reflection* means proving something by computing a `Bool` and appealing
> to a theorem that says the `Bool` being `true` implies the statement.
> [What is proved](what-is-proved.md) defines these, says what a *program*
> is and everything you can write in one, and separates what is proved from
> what is merely observed.

Unrolled traces keep theorems honest at any size, but artifacts and
kernel budgets need care at production heights (10⁶–10⁸ iterations).

## Rolled emission: small artifacts for big loops

`foldTrace` unrolling would emit gigabytes of C at 10⁷ iterations. The
rolled form (`Verified.Rolled`) compiles the body **once** with the loop
index in a dedicated counter register and emits a single `while` loop:

```lean
-- artifact: kilobytes regardless of loopCount
def emitted := emitRolled program "My.bigSweep"
```

The measured demonstration (`Testing/RolledFixedPoint.lean`): the
10⁷-iteration fixed-point checker is a **2 KB** artifact that CompCert
compiles and the native check runs in ~14 ms.

The semantics never changes: `rolledTrace_eq_augmented` proves the
rolled loop's dynamic trace evaluates exactly as the standard
`foldTrace` semantics of `Program.counterAugment p` — an ordinary
`Program` (one extra register, the increment as a source instruction),
so packaging, bridge, and denotation theorems apply to it unchanged.
Author theorems against `p.counterAugment`; emit `p` rolled.

The emitted `while` statement is inside the proved C model as well:
`Proof.evalCWhile` is a **fuelled** rule for exactly the counted shape
`rolledCFunction` emits — `u64` counter register, literal trip count,
assignment-only body ending in the increment, budget `loopCount + 1` — and
`Reflect.rolledResult_eq_denote` runs the emitted statements in that model and
gets `p.counterAugment.denote`.  Nested loops, `break`, `goto`, a `return`
inside the body, a memory-reading guard, and fuel exhaustion are all `none`:
the model declines rather than guesses.

## Arrays

`Verified.ArrayState` extends the register machine with one
bounds-guarded array (`load`/`store` return `none` out of range), with
frame lemmas and an `AProgram` denotation. Its flagship: the
smallest-prime-factor sieve sweep — a data-independent iteration space —
with `sieveSweep_cell` proving every in-bounds cell equals
`Sieve.leastFactor n`. Prefer sieves to per-element trial division:
the CompCert-compiled benchmark shows 31× in the sieve's favor.

At the fragment level, `Verified.MemFragment` brings CCIR
`load`/`store` into the proved lowering story (memory-extended states,
preservation `lowerM_correct`, production `lowerInstruction_load/store`
connections, whole-trace `lowerMSequence_correct`) under the
disjoint-single-array discipline.

## Kernel budgets at height

Three rules keep `decide +kernel` healthy:

1. **Chunk** big folds into a few-thousand-element partial computations
   combined by proved lemmas (a monolithic 150k-element pipeline was
   measured to crash the kernel — see Tutorial 3).
2. `set_option maxRecDepth 800000` in certificate files.
3. Formulate recursive helpers with arithmetic **guarded behind `if`s**
   on their arguments. Bare `Nat` subtraction/division chains at 2⁶⁴
   scale inside recursion arguments can send the kernel into runaway
   reduction ("deep recursion detected"); the guarded form — which also
   mirrors the machine realization, e.g. borrow-as-comparison — fixes
   it. (`Verified.Limb.sbbStep` and `divStep` are the canonical
   examples.)

## Batch-compiling whole projects

For the hybrid path (compiling a Lean project's generated C under
CompCert), `scripts/compile-ir-tree.py` walks a `.lake/build/ir` tree,
compiles every unit with `ccomp` (retrying once with the probe's
mechanical rewrites), and writes a JSON report. The ternary-goldbach
development's entire `Math` package — 2,273 units — compiles this way
with zero rejections (`compatibility/ternary-goldbach-2026-07-28.md`).
