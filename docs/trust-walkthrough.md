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
| assumptions | trusts Lean's compiler and runtime | **none at all** |

That last row is not a typo. Asking Lean what this theorem depends on returns
*no assumptions whatsoever* — not even the three standard axioms of ordinary
mathematics that almost every proof uses.

**What you have to trust:** Lean's kernel. That is the entire list.

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

For some programs the *meaning* defined in step 2 cannot be evaluated by Lean's
kernel either, for a mundane reason: the way the register file is represented
makes reading a register cost time proportional to the number of writes so far,
so a long loop becomes quadratic and exhausts the interpreter.

When that happens, the Lean program is not checked against the certificate by
the kernel. It is checked instead against a C implementation **written
independently from the mathematical specification**, at full production
parameters, comparing every output rather than a headline number.

That is weaker, and the affected modules say so. It is also not nothing: on one
port, an independent implementation immediately caught a bug where a helper
wrote to a register before reading it, which silently corrupted a counter and
produced a confident, badly wrong answer that every self-consistency check had
happily accepted.

## How to check any of this yourself

```console
# What does this theorem actually depend on?
#print axioms myTheorem

# Recompile every certificate with CompCert and re-run it.
# --force matters: results are cached, and a cache hit looks identical to a
# verification. Read the "0 cached, N run" split, not the exit code.
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
