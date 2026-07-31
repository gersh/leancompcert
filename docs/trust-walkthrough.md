# A complete walkthrough: from a mathematical claim to bytes

This document assumes no familiarity with Lean, CompCert, or formal
verification vocabulary. It follows two real examples all the way down and, at
every step, answers one question: **what would you have to trust for this step
to be wrong?**

By the end you should be able to look at any certificate in this repository and
say precisely what it does and does not establish.

## The problem, in ordinary terms

Sometimes a mathematical proof needs a fact that is finite but enormous — "this
inequality holds for every integer up to eight billion". Nobody checks that by
hand. A computer checks it.

That raises an awkward question: **why should anyone believe the computer?**

A proof assistant like Lean answers this for small computations. Lean has a
*kernel* — a small, heavily scrutinised program whose only job is to check
proofs. If the kernel accepts something, you are trusting a few thousand lines
of well-studied code and nothing else. The kernel can also *run* computations,
and when it does, the result carries the same weight as a proof.

The catch is speed. The kernel is built for trustworthiness, not throughput. It
handles thousands of items comfortably and billions not at all.

The usual escape hatch in Lean is a tactic called `native_decide`, which
compiles the computation and runs it at full speed. But it records that choice
as an assumption in the proof: you are now trusting Lean's compiler, a C
compiler, and Lean's runtime — several hundred thousand lines of unverified
code. For most purposes that is fine. For a proof whose entire point is that
nobody has to take your word for anything, it is a real cost.

This package exists to give you better options than "too slow" and "trust a
compiler".

## Example 1: the whole thing fits in the kernel

The best outcome is that you never leave the kernel at all.

`Ports/A36Bisect.lean` certifies a bound needed in a real analytic-number-theory
proof. It works by splitting an interval into 256 pieces and checking an
inequality on each.

That had previously been done with `native_decide`, because the kernel could
not finish it: **13.2 GB of memory and still running after 22 minutes.** The
natural conclusion is that 256 pieces is too much for the kernel. That
conclusion was wrong.

The computation used *exact fractions*. One of its steps takes a square root by
Newton's method, and each Newton step squares the denominator of the fraction —
three square roots deep, per piece. By the last piece, the numbers being
compared had tens of thousands of digits. The kernel was not struggling with
256 pieces; it was struggling with arithmetic on enormous fractions.

Rewriting the same computation in **fixed-point** arithmetic — integers scaled
by a fixed power of two, with every rounding deliberately pushed *outward* so
the answer is never accidentally made to look better than it is — gave:

| | exact fractions | fixed point |
| --- | --- | --- |
| time | **did not finish in 22 min** | **1.06 s** |
| memory | 13.2 GB | 0.64 GB |
| axioms used by the Lean proof | Lean's compiler and runtime | **none** |

That last row is real — Lean reports *no* axioms for this theorem, not even the
three standard ones almost every proof uses. **But it is narrower than it
sounds, and it is worth being blunt about how.**

The row compares the **same obligation under two mechanisms**. `native_decide`
admits Lean's compiler and runtime into the proof; `decide +kernel` admits
nothing. That difference is real and is the entire reason to prefer the kernel.

It is **not** a claim that the mathematics was proved from nothing. The
axiom-free theorem is:

```lean
theorem sweep_ok : allBelow leaves leafOK = true
```

— a *Boolean function* returns `true` on 256 integer inputs. It mentions no
real numbers (this package has no Mathlib dependency, so it could not), and
**it cannot tell you whether `leafOK` encodes the bound you meant**. Put a
wrong constant or a flipped inequality in that predicate and you get a true,
axiom-free theorem about the wrong thing. No axiom list can detect that.

**What you have to trust for this route:** Lean's kernel — *and* that the
predicate says what you think it says. The second is a separate obligation,
discussed in [the honest gap](#one-honest-gap-named) below and in
[what `#print axioms` does and does not tell you](what-is-proved.md#1b-what-print-axioms-does-and-does-not-tell-you).

**The lesson worth carrying:** before concluding that a computation is too big,
check whether it is expensive for a *representational* reason rather than a
mathematical one. This has happened three times in this project, once turning a
cost quoted in core-years into 158 seconds.

## Example 2: too big for the kernel

Now a computation the kernel genuinely cannot do: checking a bound on a sum
over every integer up to about eight billion. No representation trick rescues
that.

Here is the full chain, top to bottom.

### Step 1 — Restate the mathematics using whole numbers

The original claim involves real numbers, square roots, and infinite precision.
A computer works with whole numbers. So the first step is to write down a
statement about whole numbers only, using exact integer arithmetic, and then
**prove in Lean that the whole-number version implies the original**.

This is genuine mathematics, done separately for each claim. The strongest form
proves it *both* ways: that the integer version implies the original, and — with
a measured bound on how much stronger it is — that the original implies the
integer version too. That rules out the failure where you accidentally prove
something much weaker than you meant, or something so strong it cannot be true.

> **The subtlety that bites.** When you round, you must round in whichever
> direction makes your claim *harder* to satisfy. Which direction that is
> depends on where the quantity sits: in one real case, an upper bound on a
> difference needed the positive term rounded **up** and the negative term
> rounded **down**. Get it backwards and the reduction looks conservative while
> quietly being false. See the trap list in
> [choosing a strategy](choosing-a-strategy.md#4-traps).

**What you have to trust:** nothing new. This is a Lean proof, checked by the
kernel.

### Step 2 — Write the computation as a *program*

Not as arbitrary code, but as a value in a deliberately tiny language: a fixed
number of registers, one array, a loop whose number of iterations is fixed in
advance, and about sixteen arithmetic operations. No recursion, no `while`, no
early exit, no function calls, no floating point.

The restrictions are what make the next step possible. A loop that might run
forever cannot be reasoned about the way a loop with a known trip count can.
Everything a real computation needs beyond that list — logarithms, exponentials,
square roots — is *built* from those operations, each with its own proof.

The **meaning** of such a program (its *denotation*, if you meet that word
elsewhere) is defined mathematically: run the setup, run the body once per
index, run the finish, read the answer register. No compiler is involved in
defining what a program means.

**What you have to trust:** nothing new.

### Step 3 — Compile it, and prove the compilation is faithful

The program is translated to C, and there is a theorem — proved once, covering
every program in this language — saying:

> if the program's meaning is *n*, then running the compiled C also gives *n*.

Note the shape. It is an implication, not an equality, and that is deliberate:
the compiled code computes array addresses in 64-bit arithmetic, which wraps
around, so the reverse direction is genuinely false. Claiming an equivalence
here would be a bug, not a simplification.

**What you have to trust:** nothing new. This is a Lean proof.

### Step 4 — C to assembly: CompCert

CompCert is a C compiler with a machine-checked proof that the assembly it
produces behaves like the C it was given. This is the step where ordinary
compilers actually go wrong — large testing campaigns have found many
wrong-code bugs in mainstream compilers and essentially none in CompCert's
proved core.

**What you have to trust:** CompCert's proof, and the Coq proof assistant that
checked it. This is a well-studied artifact, but it is a genuine addition to
the list.

### Step 5 — Assembly to bytes: this is where `gcc` appears

CompCert hands three jobs to `gcc`: preprocessing the C, turning assembly text
into machine code, and linking.

**Isn't that the whole point, defeated?** No, and it is worth being precise
about why.

The proof covers the hard part — parsing, optimisation, instruction selection,
register allocation. What is delegated is mechanical: assembly is a nearly
one-to-one mapping from mnemonics to bytes, and linking resolves symbols and
lays out sections. Neither involves reasoning about what the program *means*.

The exposure shrinks further on the path this package prefers. A *freestanding*
artifact uses no C standard library at all; the compiled object has **zero
unresolved symbols**; the resulting binary is about 1.3 kB. There is very
little for a linker to get wrong when there is nothing to link.

**What you have to trust:** the assembler and the linker. That is real, and it
is stated rather than glossed. Two things reduce it in practice: the artifacts
check their own results, so a mangled binary is far more likely to fail loudly
than to lie; and every computation here is also compiled with `gcc` and
compared byte for byte, so a bug would have to strike both toolchains
identically.

### Step 6 — Actually running it

**This step is not proved, and cannot be.**

That a particular execution happened on a particular machine and printed a
particular number is a fact about the physical world. No theorem establishes
it. There are exactly two honest ways to be confident:

- **Run it again.** This is the better one. An answer anyone can re-derive
  never requires trusting whoever produced it first. The eight-billion-integer
  computation above takes about ten minutes.
- **Attested execution.** For computations where re-running would cost months
  of processor time, the run can happen inside a hardware-protected enclave
  that signs a statement naming the algorithm, its input, and its result. This
  adds an explicit, named assumption — and it establishes only that *those
  bytes ran untampered*, never that the mathematics is right.

**What you have to trust:** for the re-run route, nothing — do it yourself. For
the attestation route, the enclave hardware and its vendor.

## The two chains side by side

| | kernel route | artifact route |
| --- | --- | --- |
| Lean's kernel | ✔ | ✔ |
| Coq + CompCert's proof | — | ✔ |
| assembler, linker | — | ✔ |
| that the run happened | — | ✔ (re-run it, or attest it) |
| **typical scale** | ~10⁴ items | ~10¹⁰ items |

Use the kernel whenever it reaches. Use the artifact when it does not. Reach
for attestation only when re-running is genuinely out of the question — a
re-checkable answer is stronger evidence than any signature.

## One honest gap, named

### The question step 3 does *not* answer

Look again at what the compilation theorem says:

> if the program's meaning is *n*, then running the compiled C also gives *n*.

It relates **your program** to **the C compiled from it**. It says nothing
whatever about whether your program computes the mathematical quantity you
care about.

Those are two different worries, and it is easy to conflate them:

| worry | answered by |
| --- | --- |
| Does the machine code do what my *program* says? | step 3's theorem, then CompCert |
| Does my *program* do what the *mathematics* says? | **not by any of the above** |

The second is a question about your encoding. You wrote a few hundred register
instructions intending them to compute, say, a Möbius sum. Nothing so far
checks that they do. Get an index wrong, or a shift, and every proof in the
chain still goes through — they were never about that.

### How that question is normally answered

By running the program's meaning inside Lean's kernel on a **small
configuration** and comparing it against a simple, obviously-correct reference
— typically trial division, written directly from the definition.

If a sieve and trial division agree on every integer up to a few hundred, the
encoding is almost certainly right. That comparison is a kernel computation, so
it is a theorem, not a test. `ArraySegSieve`, `R2SegSieve` and `Prop1224Cell`
all do exactly this, and the practice is to include a configuration where the
certificate is expected to **fail** as well as one where it passes — otherwise
you cannot tell a correct encoding from one that always returns zero.

### The gap

For some programs, even the smallest meaningful configuration is too large for
the kernel to evaluate. The reason is mundane and has nothing to do with the
mathematics: the register file is represented as a chain of updates, so reading
a register costs time proportional to the number of writes made so far, and a
loop becomes quadratic. One port's smallest non-trivial configuration writes
378 registers across 351 iterations — a chain roughly 10⁵ links deep, which
exhausts the interpreter.

So for those programs **the encoding question above is never answered inside
Lean at all.**

### What is done instead, and why it is weaker

The compiled artifact is compared against a C implementation **written
independently, from the mathematical specification, by someone who never saw
the register encoding** — at full production parameters, comparing every output
value rather than a single headline number, under two different compilers.

Why this is weaker, precisely:

- It is **evidence gathered by running**, not a theorem. Agreement on the
  values tested is not agreement everywhere.
- It compares the **artifact** to the oracle. The Lean program itself is still
  never evaluated, so there remains no formal statement about what it means —
  the chain has a genuine break at exactly that link.

Why it is nonetheless worth a lot: the two implementations share no code and
were derived from different things — one from the register encoding, one from
the mathematics — so agreement on every output at production scale is hard to
achieve by accident.

And it demonstrably works. On one port, a helper that wrote its destination
register before reading its source silently turned every conditional update
into garbage; a counter reset each iteration and the artifact reported a value
off by four orders of magnitude — **confidently, with every self-consistency
check passing.** The independent implementation caught it on the first
comparison. Nothing else would have.

### What to do about it as a reader

Check which situation a given port is in — the affected modules say so in their
docstrings, and `bench/results/` records what was compared against what. A port
with a kernel-checked encoding *and* an independent oracle is in good shape. A
port with only the oracle is relying on empirical agreement for the encoding
step, and you should weigh it accordingly.

## How to check any of this yourself

```console
# What does this theorem actually depend on?
#print axioms myTheorem

# Recompile every certificate with CompCert and re-run it.
# Results are cached, but the key includes this machine's ccomp binary, its
# compcert.ini, and the machine's own identity -- so a cache hit means "this
# machine already compiled and ran exactly this C, and it agreed", not merely
# "someone, somewhere, once did".  Copying a build tree to another host will
# not produce a false pass.  Read the "0 cached, N run" split rather than the
# exit code; add --force when you want the run to happen in front of you.
lake exe lean-compcert check-native --force

# Fail the build if any certificate acquires a new assumption.
lake env lean scripts/AxiomAudit.lean
```

Reading `#print axioms` is the single most useful habit. A result showing only
the three standard axioms — `propext`, `Classical.choice`, `Quot.sound` — rests
on the kernel. Anything mentioning `native_decide` rests on a compiler as well.
Anything else is a named assumption someone chose to make, and you can go read
why.

## Where to go next

- [What is proved](what-is-proved.md) — the same material stated precisely,
  with the actual theorem statements.
- [Choosing a strategy](choosing-a-strategy.md) — which route to take, measured
  size thresholds, and the catalogue of mistakes that have produced wrong
  results here.
- [Installation](installation.md) — building CompCert.
- [The trust chain](tutorial-4-trust-chain.md) — the auditing procedure.
