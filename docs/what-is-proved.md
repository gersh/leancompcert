# What is proved, what is observed, and what "program" means

This document answers five questions that the rest of the documentation
assumes you already know: what a *program* is here, what *denotation* means,
whether this package proves an algorithm correct or merely records that it ran,
why `gcc` appears in the pipeline without defeating the purpose, and what
`check-native` actually does.

If you read only one section, read
[§3](#3-three-different-claims-dont-mix-them-up).

## 1. What a "program" is

A program here is **not** arbitrary Lean code and **not** arbitrary C. It is a
value of a small first-order datatype — a *bounded fold* over a register
machine — which is what makes it possible to prove anything about its
compilation.

```lean
structure Program where
  regCount  : Nat          -- how many registers; bounds every index used
  loopCount : Nat          -- the loop runs the index over 0 … loopCount − 1
  init      : List Instr   -- straight-line setup
  body      : List Instr   -- executed once per index
  epilogue  : List Instr   -- straight-line finish
  output    : Nat          -- which register holds the answer
```

`AProgram` is the same shape with an added array:

```lean
structure AProgram where
  regCount, arrayLen, loopCount : Nat
  init, body, epilogue : List AInstr
  output : Nat
```

**Everything you can write is this and nothing more:**

```lean
inductive Operand | reg (i : Nat) | lit (v : Nat) | idx     -- idx = the loop index
inductive Op      | add | sub | mul | udiv | urem
                  | band | bor | bxor | shl | lshr
                  | eq | ne | lt | le | gt | ge
inductive Instr   | mov (dest) (src : Operand)
                  | binop (dest) (op : Op) (lhs rhs : Operand)
inductive AInstr  | scalar (i : Instr) | load (dest idxReg) | store (idxReg srcReg)
```

That is the whole language. Note what is absent: no recursion, no
`while`, no early exit, no function calls, no floating point, no signed
arithmetic, no pointers beyond the one array. Registers hold `Nat` with the
invariant that every value stays below the word modulus, and comparisons yield
`0` or `1`.

The restrictions are the point. A loop whose trip count is fixed at
`loopCount`, over a state of `regCount` registers and one array of `arrayLen`
cells, is small enough to reason about exhaustively. Anything you want that is
not in that list — a square root, a logarithm, an early exit — has to be
*built* from it, which is what `Verified/LogFixed.lean`, `Verified/ExpFixed.lean`
and `Verified/DyadicBisect.lean` do, each with its own proof.

**Where to look for what is available:** `Verified/Reflect.lean` (the scalar
machine), `Verified/ArrayState.lean` (arrays), `Verified/AddWide.lean` and
`MulWide` (two-limb arithmetic when one word is not enough),
`Verified/LogFixed.lean` and `Verified/ExpFixed.lean` (fixed-point logarithm and
exponential, each with an exact integer bracket), `Verified/Dyadic.lean` and
`DyadicBisect.lean` (fixed-point intervals and outward-rounded square roots).
Worked programs live in `Ports/`.

## 2. Vocabulary

Three words appear constantly and are worth pinning down.

**Denotation** — *what a program means*, computed as ordinary Lean arithmetic.
`p.denote` runs the program's `init`, then its `body` once for each index, then
its `epilogue`, and reads the output register. It returns `Option Nat`: `none`
when something is undefined (an array index out of range), `some n` otherwise.
Think of it as "the answer this program is supposed to give", defined
mathematically rather than by running anything. Wherever this documentation
says *denotation*, it means exactly that.

**Compilation** — `p.compile` turns the same value into a CompCert C program.

**Reflection** (or *proof by reflection*) — proving a statement by computing a
`Bool` and appealing to a theorem that says "this `Bool` being `true` implies
the statement". The computation replaces a hand-written proof.

## 3. Three different claims — don't mix them up

This is the part that matters, and where it is easiest to overclaim.

Getting from *a theorem about the integers* to *a number an artifact printed*
involves **three separate steps, only two of which are proved**.

### (a) The reduction — proved, per atom, in Lean

A real-valued mathematical claim is restated as one about naturals with exact
integer arithmetic, and that restatement is proved not to weaken the original.
This is where the mathematics lives, and it is done **separately for each
statement** — see `Ports/` and the corresponding reductions. The strongest form
is two-sided: the family implies the statement, the reduction is at most some
measured amount stronger, and the converse holds given that slack.

### (b) The compilation — proved once, for all programs

```lean
theorem AProgram.evalCC_compile (p : AProgram) (hWF : p.WF) (base : Int)
    (hBase : BaseOk p.arrayLen base) (n : Nat) (hDenote : p.denote = some n) :
    Option.bind (evalMCCSequence (p.initialMCC base) p.compile)
      (fun m => m.env ⟨p.output + 1⟩) = some ((n : Nat) : Int)
```

In words: **if the program's denotation is `n`, then running the compiled C
gives `n`.** CompCert's own Coq proof then carries that from C to assembly.

Note the direction. It is stated as *denotation defined ⇒ C agrees*, not as an
equality, and that is deliberate: the compiled address arithmetic happens in
64-bit words, so `i ↦ (8i + base) mod 2⁶⁴` is not injective, and the reverse
implication is genuinely false. Claiming an `iff` here would be a bug.

### (c) The run — **observed, not proved**

Nothing in this package proves that a particular execution happened or that it
printed a particular number. That is an empirical fact about a machine, and it
is established one of two ways:

- **re-running it** — cheap, and strictly the better evidence, because a
  re-checkable answer never requires trusting whoever produced it; or
- **attested execution** — a TDX quote, for cases where re-running costs months
  of CPU. This adds a named axiom.

So: **this package proves that the algorithm you wrote is faithfully translated
to machine code, and (separately, per atom) that the algorithm computes
something that implies your theorem. It does not prove that any given run
occurred.** A log is a log.

### One more gap, stated plainly

For some programs the denotation cannot be evaluated in Lean's kernel at all.
`denote` threads the register file as a closure chain — one link per write — so
reads cost `O(writes so far)` and the whole loop is quadratic. A body writing
several hundred registers over a few hundred iterations is already ~10⁵ links
deep and defeats the interpreter.

When that happens, **the Lean model is not checked against the certificate by
the kernel**; it is checked against an independently written C oracle at
production parameters instead. That is weaker, it is stated in the affected
modules, and you should know which of your ports are in that situation.

## 4. Why `gcc` is in the pipeline, and why that is not self-defeating

`compcert.ini` contains:

```
prepro=gcc
asm=gcc
linker=gcc
prepro_options=-U__GNUC__ -E
```

so CompCert delegates **preprocessing, assembly, and linking** to `gcc`. This
is a fair thing to be suspicious about. The honest answer has three parts.

**First, the proof covers the step where compilers actually go wrong.**
CompCert's semantic-preservation theorem is about C → assembly: parsing,
type-checking, optimisation, instruction selection, register allocation,
scheduling. That is where real miscompilations live — random-program testing
campaigns have historically found hundreds of wrong-code bugs in mainstream
compilers and essentially none in CompCert's proved middle end. Preprocessing,
assembling, and linking are not that step.

**Second, the delegated steps are mechanical, not semantic.** Assembly is a
near one-to-one mapping from mnemonics to bytes. Linking resolves symbols and
lays out sections. Preprocessing is textual substitution — and note
`-U__GNUC__`, which undefines the macro so that system headers do not take
gcc-specific code paths.

**Third, and best: the freestanding path makes the delegated work nearly
trivial.** A freestanding artifact uses no libc; the CompCert object has **zero
undefined symbols**; the only glibc references in a default build
(`__libc_start_main`, `abort`) come from gcc's startup glue, which the
freestanding build does not use. Measured on aarch64: 70,504 bytes dynamic by
default versus **1,328 bytes static** freestanding. There is very little left
for the linker to get wrong, and the entry stubs in `runtime/start/` are five
instructions each — outside the theorem, but auditable at a glance.

**But it is not zero.** The assembler and linker are trusted, full stop, and
[the trust chain](tutorial-4-trust-chain.md) says so. Two things reduce the
exposure in practice: artifacts are self-checking, so a mangled binary is
overwhelmingly likely to fail rather than lie; and every port in this
repository is differentially tested against a `gcc`-compiled build of the same
source, with byte-identical results on every output slot — which is a genuine
cross-check of both toolchains, since a bug would have to hit both identically.

If you want to shrink the trusted set further, `ccomp -S` on the host emits the
assembly — the proved step — and you can assemble and link wherever you like,
including inside a container for another architecture. Moving those steps
changes nothing about what is proved, precisely because they were never inside
the theorem.

## 5. `check-native`

### What it does

```console
$ lake exe lean-compcert check-native
[run] mertens: compiled with CompCert (freestanding), native check passed
...
native check: 11 certificates agree with their certified values (0 cached, 11 run, freestanding link)
```

For each **registered** certificate it emits the C, compiles it with `ccomp`,
links it freestanding, runs the binary, and compares the result against the
value the Lean certificate claims.

### What it is not

**The binary's exit status is never admitted as a theorem.** Nothing in the
Lean development says "this ran and returned 0". `check-native` is a
*cross-check*: it catches a mismatch between what your Lean program means and
what the compiled artifact does — an encoding bug, a stale certificate, a
mis-registered value. The certificate's own proof stands on the kernel, and
`#print axioms` on it should show the base trio and nothing else. If a
certificate needs `check-native` to pass in order to be believed, something has
gone wrong upstream.

### Wiring it into your project

1. Write your program as a `Program`/`AProgram` in a `Ports/` module and prove
   `…_wf` and `…_compiled` against `AProgram.evalCC_compile`.
2. Register it in the certificate list that `check-native` iterates
   (`LeanCompCert/Main.lean`), giving its name, its generated C, and its
   certified value.
3. Add the new theorems to `scripts/AxiomAudit.lean` so an axiom regression
   fails the audit rather than passing silently.
4. Run it in CI.

A complete worked consumer, including the five-line wiring, is in
[`examples/consumer/`](../examples/consumer/).

### Making sure the verification is actually done

`check-native` is cached, and a second run reports `[cached]` without compiling
anything. The question is what a cache hit is worth.

**The stamp is keyed to this machine's toolchain, not just to the source.** It
covers the generated C, the include configuration, the header directories, the
link mode, the assembler and linker versions, the startup stub — and the
**digest of the `ccomp` binary together with the full text of its
`compcert.ini`**.

That last part matters more than it looks. `ccomp -version` prints only

```
The CompCert C verified compiler, version 3.17
```

with **no architecture**. A CompCert configured `aarch64-linux` and one
configured `x86_64-linux` are indistinguishable by version string, and
cross-compiling is a normal setup here. `arch`, `abi`, and the
prepro/asm/linker options all live in `compcert.ini`. Hashing it is what stops
a stamp written by one install from being honoured by the other; hashing the
binary additionally catches a CompCert rebuilt from patched sources at the same
release number.

**The stamp is also bound to the machine.** Without that, the cache directory
is portable: copying `.lake/build/native-check/` to another host carries the
stamps *and* the compiled binaries, so a machine that never ran anything
reports `cached` and `pass`. A shared Docker layer, a restored backup, or an
`rsync` of a checkout produces that by accident. The key includes
`/etc/machine-id` (falling back to dbus's copy, then hostname plus
`uname -m -s`).

So a `[cached]` line now means: *this machine, with this CompCert install,
already compiled and ran exactly this generated C, and it agreed.* Change the
compiler, its target, the stub, the headers, the program, **or the machine**,
and the stamp is discarded automatically.

**But understand what that is and is not.** This makes the cache *honest*, not
tamper-proof. The stamp is an unsigned file in a directory you own; anyone who
can copy it can also edit it. It defends against a build tree arriving from
somewhere else — the realistic failure — not against someone determined to
forge a pass. Evidence that survives an adversary has to be re-run, or run
under attestation.

If you are deliberately sharing a cache between identical containers, set
`LEAN_COMPCERT_SHARED_CACHE=1` and accept that a hit no longer means "it ran
here".

**When you still want `--force`:**

- you are **producing evidence for someone else**, and want the compile and the
  run to have happened in front of you rather than be attested by a file you
  also control;
- you want **real timings**;
- you suspect the cache directory itself.

**And regardless: read the summary line, not the exit code.**

```
native check: 11 certificates agree ... (0 cached, 11 run, freestanding link)
```

`0 cached, 11 run` is a verification you just watched. `11 cached, 0 run` is a
record that one happened. Both are green.

The same discipline applies to the other gates: `#print axioms` should be read,
not assumed, and `scripts/AxiomAudit.lean` should be run rather than trusted to
have been run.

## See also

- [Choosing a strategy](choosing-a-strategy.md) — which route to take, the
  measured thresholds, and the trap catalogue.
- [The trust chain](tutorial-4-trust-chain.md) — what is proved where, and what
  is trusted.
- [Installation](installation.md) — building CompCert, and what `arch=x86`
  means.
