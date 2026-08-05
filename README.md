# lean-compcert

**In plain terms.** Some proofs need a fact that is finite but enormous —
"this holds for every integer up to eight billion". A computer checks it. The
awkward question is why anyone should believe the computer.

Lean's kernel is a small, heavily scrutinised proof checker; if it accepts a
computation, you are trusting a few thousand lines of well-studied code and
nothing else. But it is built for trustworthiness rather than speed, and stops
being practical somewhere around ten thousand items. The usual escape hatch,
`native_decide`, runs the computation at full speed but records that choice as
an assumption — you are now trusting Lean's compiler and runtime too.

This package gives you better options than "too slow" and "trust a compiler":
push far more into the kernel than you would expect, and when that genuinely
runs out, fall back to a compiled artifact whose translation is *proved*
faithful rather than assumed.

**→ [Read the complete walkthrough](docs/trust-walkthrough.md)** — two real
examples followed from a mathematical claim all the way to bytes, assuming no
familiarity with Lean or CompCert, answering at every step: *what would you
have to trust for this to be wrong?* Start there if any of the vocabulary
below is unfamiliar.

One thing worth knowing up front, because it is the most common confusion:
this package proves that your algorithm is faithfully translated to machine
code, and separately that your algorithm implies your theorem. **It does not
prove that any particular run happened.** That comes from re-running the
computation, or from attested execution. See
[what is proved](docs/what-is-proved.md).

---

`lean-compcert` turns finite Lean computations into kernel-checked
theorems and [CompCert](https://compcert.org/)-compiled native
artifacts. It serves two use cases:

**1. A verified `native_decide`.** `native_decide` is fast but proves
things by axiom (`Lean.ofReduceBool` — trust Lean's compiler, a C
compiler, and the runtime); plain `decide` is trustworthy but too slow
at scale. This package gives you both halves: the theorem is checked by
**Lean's kernel only** (standard axioms — `#print axioms` shows no
native trust), while fast native runs come from CompCert-compiled
self-checking binaries via the cached `check-native` pipeline — nothing
re-runs when you recompile unless the generated code actually changed.
→ **[How to do it](docs/use-case-1-verified-native-decide.md)**

**2. A compiled artifact you can trust.** When you want the binary
itself: a Lean theorem states what the emitted C computes, Coq's kernel
proves CompCert's own semantics assigns it the certified value (on the
direct path), and CompCert's machine-checked theorem carries that to
assembly. → **[How to do it](docs/use-case-2-verified-artifact.md)**

**3. An artifact run admitted into a proof — opt in, and visibly.** When the
computation is too big for the kernel *and* too expensive for anyone to re-run,
`LeanCompCert/Trusted/` admits the execution through one statement,
`EvidencedRun`, instantiated once per use site so that `#print axioms`
enumerates every admitted run by name. The premise is an inspectable evidence
record — artifact digest, toolchain, machine, shard, challenge nonce, verdict —
that Lean's kernel re-checks. Nothing in the `LeanCompCert` library imports it,
so **depending on this package still adds nothing to your axiom list** unless
you ask for it. → **[How a computation enters a proof](docs/incorporating-a-computation.md#route-c--admit-the-execution-through-one-opt-in-axiom)**

The guides state exactly *what is proved* and *why the method deserves
trust*; the boundary is drawn honestly in each.

It does **not** claim end-to-end verified compilation from Lean. When generated
C is accepted by CompCert, only the C-to-assembly portion receives CompCert's
semantic-preservation guarantee, subject to CompCert's assumptions and external
functions. For general application code (the hybrid driver and LCNF
paths below), the Lean frontend and C emitter, normalization, runtime,
atomics adapter, assembler, linker, external libraries, operating system,
and hardware remain in the trusted boundary; for fragment certificates,
the guides above give the much tighter story.

The development plan toward a generic, consumable verified-computation
package — milestones, acceptance criteria, trust commitments, and
non-goals — is in [ROADMAP.md](ROADMAP.md); all seven milestones are
implemented, with per-milestone evidence recorded there.

## Documentation

**New to any of this?** [The complete walkthrough](docs/trust-walkthrough.md)
— no assumed vocabulary, two real examples traced from a mathematical claim to
bytes, naming what you must trust at each link.

**Have a computation and need it inside a proof?**
**[How a computation enters a proof](docs/incorporating-a-computation.md)** —
the three routes, what each requires, and which are complete. The short answer
most people need: for anything someone can re-run, you do **not** get the run
into Lean at all. You state the theorem conditionally on the computation's
verdict and ship a reproducible artifact — which is not a workaround but the
better shape, since it makes the obligation explicit and lets a sceptic
discharge it themselves.

**Ready to write one?** [How to actually write a program](docs/writing-a-program.md)
— you do not write assembly: arithmetic goes through `expr!( … )` and is
compiled *with a proof*, and you build the rest from ordinary Lean emitter
functions. The guide covers what changes when there is no branch and no early
exit (gates, violation counters, checked budgets), where the word size binds,
the four proof obligations you owe, and a checklist of the mistakes that have
actually produced wrong answers here.

**Starting from an ordinary algorithm and a mathematical specification?**
[From an algorithm to a mathematical proof](docs/algorithm-to-proof.md)
documents the reusable `Algorithm.Ensures` → `ProgramRefinement` →
`ProgramClaim` path, including where `mvcgen` helps and the explicit boundary
where an independent `gpu_prover` supplies remote execution evidence.

**Setting up?** [Installation](docs/installation.md) — building CompCert,
verifying it, and requiring this package from your `lakefile.toml`.

**Want to know what this actually proves?** Read
**[What is proved, what is observed, and what "program" means](docs/what-is-proved.md)**
first. It defines the little register-machine language you write in and lists
everything it contains; explains *denotation* and the other recurring terms;
separates the three claims that are easy to conflate — the reduction (proved),
the compilation (proved), and the run itself (**observed, not proved**);
explains why `gcc` appears in the pipeline without defeating the purpose; and
says what `check-native` does, how to wire it in, and why a cached pass is not
evidence that anything ran.

**New here, or holding a slow `native_decide`?** Start with
**[Choosing a strategy for a finite computation](docs/choosing-a-strategy.md)**.
It routes you to the right approach — kernel, compiled artifact, or attested
run — with the measured thresholds that separate them, and it catalogues the
mistakes that have actually produced wrong or vacuous results here. Its first
section is the one people skip: check whether your computation is slow for the
*wrong reason* before concluding it is infeasible. Exact `ℚ` in a kernel loop
turned a 256-leaf certificate from "13.2 GB, unfinished at 22 minutes" into
1.06 s, and moved it off `native_decide` onto the kernel.

**A warning about that second clause, and about every axiom count in these
docs.** `#print axioms` on that certificate reports no axioms — which is true,
and much narrower than it sounds. The theorem says a Boolean function returns
`true` on 256 integer inputs. It does not mention real numbers, and it cannot
tell you whether the predicate encodes the bound you meant. A low axiom count
compares *like with like* — the same obligation under `native_decide` versus
under the kernel — and is **not** a summary of the trust surface. See
[what `#print axioms` does and does not tell you](docs/what-is-proved.md#1b-what-print-axioms-does-and-does-not-tell-you).

Then the use-case guide that matches your goal:

- **[Use case 1 — a verified `native_decide`](docs/use-case-1-verified-native-decide.md)**
  — kernel-checked certificates with cached CompCert-compiled native
  cross-checks.
- **[Use case 2 — a compiled artifact you can trust](docs/use-case-2-verified-artifact.md)**
  — emission, the verification gates, and the Coq-side semantics
  theorem.
- **[Use case 3 — attested run receipts](docs/use-case-3-attested-run-receipts.md)**
  — for computations too large for the kernel: a signed record of a run,
  bound to the emitted C by a digest the kernel checks, and one named
  axiom for the one thing no proof establishes.  A locally signed receipt
  is **tamper-evident, not attested**, and the guide says so throughout.
- **[The program ledger](docs/program-ledger.md)** — one view of every
  registered program: what is in it, and which of three *independent*
  states it is in.  `lake exe lean-compcert ledger` prints **compiled**,
  **run** and **chain proved** as separate columns and never merges them;
  a program whose C changed since its last run reads **stale**, not run;
  and `describe NAME` answers "what does this binary actually compute?"
  without reading the emitter.

Deep-dive tutorials in [docs/](docs/):

1. [Your first certificate](docs/tutorial-1-first-certificate.md) — from
   a register program to an axiom-audited theorem and a CompCert-checked
   native run.
2. [Wide arithmetic](docs/tutorial-2-wide-arithmetic.md) — 128-bit
   accumulators, the limb layer, dyadic fixed-point intervals.
3. [Replacing `native_decide`](docs/tutorial-3-replacing-native-decide.md)
   — the three-layer equivalence architecture, the proved equivalence
   library, and the kernel-scale chunking discipline.
4. [The trust chain](docs/tutorial-4-trust-chain.md) — what is proved,
   where, and how to audit it; the four artifact verification gates.
5. [Loops, arrays, and scale](docs/tutorial-5-loops-and-scale.md) —
   rolled emission, the array machine, batch project compilation.

A complete external-consumer walkthrough — including the five-line
`check-native` wiring — lives in
[examples/consumer/](examples/consumer/).

## Quick start

Requirements:

- Lean 4.30 or newer (the repository pins Lean 4.32.1);
- Python 3.11 or newer;
- CompCert's `ccomp` on `PATH`, or an explicit `--ccomp` path.

`ccomp` is not packaged by most distributions and has no official binaries, so
it must be built from source — see **[Installation](docs/installation.md)** for
the build, the two configure traps that cost an afternoon (Menhir discovery,
and the absence of any `-target` flag), how to add this package to a Lean
project, and how to wire the `check-native` cross-check. Run
`./bin/lean-compcert doctor` to confirm the pieces line up.

Build and differentially test a Lean executable directly from a checkout:

```console
./bin/lean-compcert build Main.lean
```

Or install the command in an isolated environment:

```console
python3 -m venv .venv
.venv/bin/pip install -e .
lean-compcert build Main.lean
```

The default output is `.lake/build/lean-compcert/<module>/`, containing:

- Lean's generated C and a mechanically normalized copy when required;
- a CompCert object and linked executable;
- a conventional reference executable used for differential testing;
- `build-manifest.json`, including exact commands and the trust boundary;
- `report.json`, a machine-readable build/provenance report;
- `report.md`, a minimized human-readable compatibility report;
- CompCert preprocessing and intermediate outputs.

The other driver commands are:

```console
./bin/lean-compcert emit-c Main.lean
./bin/lean-compcert compile-ir Main.lean
./bin/lean-compcert check-runtime
./bin/lean-compcert doctor
```

`build` compares stdout, stderr, and exit status with Lean's standard C backend
by default. Use `--no-differential-check` only when a reference run is not
wanted. Common controls include `--ccomp`, `--target`, `--profile`,
`--runtime`, `--opt-level`, `--debug-symbols`, `--reject-unsafe`, and
`--report`. Each build also writes `abi-manifest.json`; pass its
`runtimeAbiHash` back through `--expected-runtime-abi-hash` to make a later
build fail if Lean's ABI headers or the runtime shim changed.

## Compatibility probe

For low-level reconnaissance without the build-manifest wrapper:

```console
./bin/lean-compcert-probe Main.lean
```

Its default output is `.lake/build/lean-compcert-probe/<module>/`.

Useful options:

```console
lean-compcert-probe Main.lean \
  --ccomp /opt/CompCert/ccomp \
  --target x86_64-linux \
  --attempt-rewrites \
  --differential-check
```

Mechanical rewrites are made only in a separate `*.rewritten.c` copy. To compare
automatically built executables with arguments, repeat `--run-arg`. To compare
two already linked executables instead:

```console
lean-compcert-probe Main.lean \
  --reference-command "./build/Main-standard arg" \
  --candidate-command "./build/Main-compcert arg"
```

Both command options are required together. Standard output, standard error,
and exit status must all match.

The normalizer handles Lean's static flexible-array initializers for strings,
constructors, closures, object arrays, and scalar arrays. These rewrites use
fixed-size anonymous structures (or omit a zero-length tail member) while
preserving the documented Lean field order.

The driver and probe default to the hybrid runtime boundary. Their CompCert
include path shadows `<stdatomic.h>` with a narrow ABI-preserving declaration
and links `runtime/adapters/atomics.c`, compiled by Lean's host compiler.
Reports identify this adapter, the prebuilt Lean runtime, assembler, linker,
and system libraries as outside the CompCert-compiled application boundary.

The probe automatically uses `lake env lean` when the input belongs to a Lake
package, allowing package imports to resolve normally.

## Implementation status

The repository implements its initial engineering objective with two
deliberately separate pipelines.

### Executable hybrid pipeline

`lean-compcert build` asks the pinned Lean frontend to emit application C,
applies only the recorded mechanical normalizations, compiles every generated
application translation unit with CompCert, links the conventional atomics
adapter and prebuilt Lean runtime, and differentially runs the result against a
conventional Lean build.

Implemented:

- `build`, `emit-c`, `compile-ir`, `check-runtime`, and `doctor`;
- CompCert preprocessing, compilation, linking, execution, and differential
  stdout/stderr/exit-status checks;
- exact command and compiler-version provenance;
- standalone runtime ABI and build manifests;
- runtime ABI drift rejection;
- machine-readable runtime classification;
- deterministic flexible-array normalization for Lean static constructors and
  strings;
- the Version 0.1 list/closure/IO acceptance program;
- an allocation/reference-count stress workload.

### Direct LCNF pipeline

`lean-compcert compile-ir` installs the Lean 4.32 impure-LCNF pass, converts
compiler data through the stable `LeanCompCert.LCNF` view, validates it, lowers
supported declarations to typed CCIR, validates the restricted typed C AST,
emits CompCert-compatible C, and compiles every successfully lowered
declaration to an object with `ccomp`.

Implemented directly from LCNF:

- fixed-width scalar types and literals;
- first-order functions and direct calls;
- modular arithmetic, comparisons, and shifts;
- explicit control flow and constructor cases;
- object constructors, object-field stores/projections, retain, and release;
- precise per-declaration rejection artifacts.

Currently rejected by the direct path:

- boxed `Nat`/`Int` and erased/tagged wrapper operations;
- closure allocation, partial application, and indirect calls;
- scalar constructor-field layouts and destructive reset/reuse;
- join points requiring block-parameter/phi lowering;
- full IO and module initialization.

The hybrid pipeline is therefore the usable Version 0.1 executable path. The
direct LCNF path is the architecture for replacing ordinary Lean C emission as
the supported subset expands. The general `build` command currently uses Lean's
ordinary C emitter followed by narrowly defined normalization, keeping the
manifest honest about what lies outside CompCert's C-to-assembly theorem.

For compiler-API reconnaissance, importing
`LeanCompCert.CompilerAdapter.Pass` installs a Lean 4.32 impure-LCNF capture
pass. Set `LEAN_COMPCERT_LCNF_DIR` while compiling to write deterministic
per-declaration stable-view artifacts. Direct Lean compiler API usage is
isolated in `LCNF/AdapterV4_32.lean`.

The Lean library includes a typed CCIR, validator, interpreter, restricted
C AST, Profile 1 validator/emitter, ABI model, and pure first-order lowering.
The `lean-compcert` executable exposes a runnable integration program:

```console
lake build
.lake/build/bin/lean-compcert demo
.lake/build/bin/lean-compcert emit-demo-c .lake/build/integration/pure.c
ccomp -Iruntime/include -I"$(lean --print-prefix)/include" \
  -o .lake/build/integration/pure .lake/build/integration/pure.c
.lake/build/integration/pure
```

## Machine-checked semantic-preservation proof

`LeanCompCert/Proof/PureSemantics.lean` contains a machine-checked Lean proof
for the current scalar, straight-line core: semantic preservation for
arbitrary-length straight-line traces containing scalar assignments, ten
unsigned fixed-width binary operations, and six unsigned comparisons. It
proves a theorem about the production lowering functions; it is not a claim of
whole-Lean verified compilation.

The source state maps `CCIR.LocalId` values to mathematical integers, the
target state maps emitted C identifiers to integers, and `EnvRel` says that
`ABI.localName id.value` contains the value of source local `id`. The CCIR and
C models define their type widths, normalization, and binary operators
separately; `bitWidth_lowerType`, `normalize_lowerType`, and
`evalBinary_lowerType` prove that the corresponding scalar computations agree.
Division and remainder by zero evaluate to `none`.

The proved instruction fragment contains scalar assignment; unsigned add,
subtract, multiply, divide, and remainder; unsigned bitwise and, or, and xor;
unsigned left and logical-right shifts; the unsigned comparisons
`==`, `!=`, `<`, `<=`, `>`, and `>=`; and width-conversion casts whose target
is the destination type. Comparison instructions carry a decidable side
condition that their operands lower to non-signed C expressions, which is
exactly the cast-free case of the production comparison lowering.

The proof is layered:

1. `lowerOperand_correct` proves operand lowering.
2. `lowerBinary_unsigned_correct` proves expression lowering for every
   supported unsigned binary operation.
3. `lowerAssignment_correct` and `lowerBinary_assignment_correct` prove that
   source and target assignment steps preserve `EnvRel`.
4. `lowerStraight_is_lowerInstruction` proves that a successfully produced
   statement is exactly the statement returned by the production
   `Lower.lowerInstruction`, not a duplicate test compiler.
5. `lowerSequence_is_lowerInstructions` lifts that syntactic connection to
   arbitrary-length traces.
6. `lowerSequence_correct` proves semantic preservation for every successfully
   lowered, well-formed trace by induction over its length.

Bounded loops enter the fragment as unrolled traces: `foldTrace count body`
concatenates the straight-line body of each iteration, and
`lowerSequence_append`, `evalCCSequence_append`, and
`evalCCSequence_foldTrace` prove that lowering and evaluation decompose along
the unrolling, so `lowerSequence_correct` covers the whole fold as one trace
and specifications can be related to ordinary Lean folds by induction on the
iteration count.

There are no proof placeholders or axioms in this proof module. `lake build`
kernel-checks all the theorems. Check the proof alone with:

```console
lake build LeanCompCert.Proof.PureSemantics
```

### Exact boundary

This closes a useful first proof obligation:

```text
straight-line scalar CCIR
        ≈
restricted generated-C computation model
```

The next boundary — this restricted C model versus **CompCert's own
Clight semantics** — is closed for the straight-line certificate fragment by
the M6
bridge (see [use case 2](docs/use-case-2-verified-artifact.md) and
[Tutorial 4](docs/tutorial-4-trust-chain.md)): `clightgen -normalize`
translation validation of every certificate unit, a structural
correspondence checker plus the same correspondence re-checked inside
Coq's kernel at `Qed`, and — for straight-line certificates — direct
Clight emission with a Coq-kernel theorem that CompCert's bigstep
semantics (`ClightBigstep.eval_funcall`) computes the certified value
for every global environment and memory.  Generic Coq soundness theorems now
also cover fuelled rolled control flow and pointer-backed loads/stores
(`scripts/coq/ClightMemorySem.v`) against CompCert's real memory model.
Production arrays use pointer-typed indexed CCIR operations and lower to
`base[index]`. `Verified.ArrayRolled` proves that their counter-driven rolled
trace has the same CCIR-with-memory semantics as the literal-index trace used
by the Lean denotation proof. The Coq memory development proves the flat-array/
CompCert-block load/store relation, including preservation across stores, and
`scripts/clight-array-verify.py` specializes the generic theorem to the
complete `clightgen` AST of the production Möbius array function. The remaining
artifact-specific development now includes a sparse flat-array evaluator, a
proved simulation of every supported flat execution into actual CompCert
memory, and a theorem deriving its zero-array relation from CompCert's real
`Init_space` global initialization.  A fast kernel computation also obtains
`99952` for the specialized production step.  What remains is the refinement
lemma identifying that specialized step with one iteration of the exact
Clight body; until then the exact-AST function theorem remains conditional on
a successful flat execution. The Coq-side gates need a
CompCert Coq development (or `clightgen`) installed; a compiler-only
`ccomp` installation still gets the Lean-side proof and the Python
structural checker, and the acceptance suite skips the Coq gates
gracefully.

Boundaries that remain open, stated plainly:

```text
Lean / LCNF semantics  →  CCIR        (not proved; certificates instead
                                       *state* their theorem at the CCIR
                                       denotation, so nothing is trusted here)
full CCIR control flow, calls, heap    (outside the fragment; loops enter
                                       as proved traces, arrays under the
                                       disjoint-single-array discipline)
```

The hybrid path that recompiles Lean's ordinary emitted C is not covered
by this proof.

## `verified_decide`

`LeanCompCert.Verified.Decide` provides two axiom-free proof modes built on the
proof above.

For a closed, total, kernel-reducible proposition, use the drop-in form:

```lean
example : (List.range 1000).length = 1000 := by
  verified_decide
```

This expands to `decide +kernel` with a larger local recursion allowance
(`maxRecDepth := 100000`). It does not invoke native code.

For a computation packaged in the proved compiler fragment, use:

```lean
import LeanCompCert.Verified.Decide

example : computation.Returns 42 := by
  verified_decide using
    LeanCompCert.Verified.Decision.forResult computation 42
```

A complete runnable example is in `LeanCompCert/Testing/VerifiedDecide.lean`.

`Verified.Computation` packages a CCIR function and straight-line instruction
trace, the corresponding restricted-C statements, a well-formedness proof, a
proof that the statements were returned by the production lowering function,
and the local containing the result. `Computation.result_preserved` proves that
evaluating the generated-C model returns exactly the result of evaluating the
CCIR model. `Verified.Decision p` adds an accepting result and a
once-per-algorithm specification, `computation.Returns acceptingValue ↔ p`;
after that specification is proved, each closed instance can use
`verified_decide using decision`.

### Why this does not use `native_decide`

`native_decide` obtains speed by trusting a native evaluator through a special
axiom. `verified_decide` intentionally uses Lean's kernel-checkable `decide`
on the closed CCIR result equality. The native CompCert executable may be run
as a fast independent check, but its exit status is not admitted as a theorem.

The no-argument form is a sound substitute when kernel reduction can expose
the computation. The `using` form additionally connects a supported CCIR
computation to the restricted generated-C model. Neither form can prove facts
about opaque or `partial` definitions unless those definitions provide logical
specifications.

Run the packaged example through CompCert:

```console
lake build
.lake/build/bin/lean-compcert emit-verified-decide-c /tmp/verified-decide.c
ccomp -Iruntime/include -I"$(lean --print-prefix)/include" \
  -o /tmp/verified-decide /tmp/verified-decide.c
/tmp/verified-decide
```

The executable returns zero when the compiled computation returns 42.

### The cached native cross-check: `check-native`

The manual emit/ccomp/run loop above is packaged as a single cached
command over every registered certificate:

```console
lake exe lean-compcert check-native
```

For each certificate it emits the generated C (whose `main` returns 0
exactly when the computed value equals the certified constant), compiles
it with `ccomp`, runs it, and records a stamp keyed by the **content
hash of the generated C** plus the ccomp version. On later runs,
certificates whose C is unchanged are reported `[cached]` and skipped;
only certificates whose generated C actually changed are recompiled and
re-run. Change tracking is therefore two-layered: Lake rebuilds the
`lean-compcert` executable when certificate Lean sources change, and the
runner re-emits and re-hashes the C to decide what to re-run. `--force`
re-runs everything; `--dir DIR` relocates the cache (default
`.lake/build/native-check`); `--include DIR` adds a C include path
(repeatable; used by consumer projects). Stamps are written only on a passing run,
so failures always retry.

This is the `native_decide` *workflow* — fast native execution on every
change — with the trust split kept intact: the theorem is established by
`verified_decide` in Lean's kernel, and the CompCert-compiled run is an
independent cross-check whose exit status never becomes a premise. The
acceptance suite runs `check-native` twice and fails if the second run
is not fully cached.

### Current fragment

The computation proof supports straight-line scalar assignment; unsigned
fixed-width add, subtract, multiply, divide, remainder, bitwise
and/or/xor, left and logical-right shifts; the six unsigned comparisons;
width-conversion casts; memory `load`/`store` under the
disjoint-single-array discipline (`Verified.MemFragment`); multi-word
accumulation (demonstrated at 128 bits, with the arbitrary-precision limb
layer behind it); bounded loops as unrolled `foldTrace` traces with the
rolled emission proved equivalent (`Verified.Rolled`); and data-dependent
recursions via the proved equivalence library (early-exit folds, gcd,
sqrt, least-factor scans — see Tutorial 3). General CCIR `branch`/`goto`
control flow and heap objects beyond the array discipline remain outside
the fragment; the equivalence architecture is how real recursive
algorithms enter it.

## Goldbach-style fold certificates

The concrete target for this fragment is the certificate shape used by
computational number-theory developments such as
[ternary-goldbach-lean](https://github.com/gersh/ternary-goldbach-lean),
whose `native_decide` certificates are folds of scaled integer floor-sums
over filtered ranges, for example
`125415339420275877467 ≤ oddMertensList.foldl oddMertensLoStep 0`.

`LeanCompCert/Testing/MertensCertificate.lean` builds that certificate shape
inside the proved fragment. A bounded fold over `1 ≤ q ≤ 99` filters odd `q`
with a proved comparison instruction and accumulates `⌊2¹⁶/q⌋` with proved
unsigned division, shift, and addition instructions:

```lean
theorem referenceSum_eq : referenceSum = expectedValue := by
  verified_decide using decision

theorem referenceSum_ge : expectedValue ≤ referenceSum
```

`#print axioms referenceSum_eq` reports only `propext`: no `native_decide`,
no `ofReduceBool`, and no other native-evaluation axiom. The same packaged
computation is emitted as restricted C, compiled by CompCert, and executed as
an independent native check:

```console
lake build
.lake/build/bin/lean-compcert emit-mertens-cert-c /tmp/mertens-cert.c
ccomp -Iruntime/include -I"$(lean --print-prefix)/include" \
  -o /tmp/mertens-cert /tmp/mertens-cert.c
/tmp/mertens-cert
```

The executable exits zero exactly when the CompCert-compiled fold returns the
certified value. The acceptance suite performs this check automatically.

### The production scale: 128-bit accumulation from proved 64-bit steps

The production Mertens certificates scale by `2⁶⁴`, so their accumulators
exceed the machine word (`oddMertensLoAcc ≈ 6.8·2⁶⁴`).
`LeanCompCert/Testing/WideMertensCertificate.lean` certifies a fold at that
exact scale:

```lean
theorem referenceSum_eq :
    referenceSum = 54192380775997480166 := by  -- = 2·2⁶⁴ + lo
  verified_decide using decision

theorem referenceSum_ge : 2 * certScale ≤ referenceSum
```

Everything wider than 64 bits is built from proved instructions: the term
`⌊2⁶⁴/q⌋` is `⌊(2⁶⁴−1)/q⌋` plus a proved-comparison increment, the
accumulator is a `lo`/`hi` pair of `u64` locals whose carry is the proved
comparison `lo' < lo` widened by a proved cast, and the certificate output is
an in-circuit acceptance flag checking both words. `#print axioms` again
reports only `propext`. The same computation compiles and runs under
CompCert via `emit-wide-mertens-cert-c`.

### The production per-element mathematics: squarefreeness and totients

`LeanCompCert/Testing/SquarefreeMertensCertificate.lean` certifies the exact
§14.1 `oddMertensLoAcc` shape — `Σ_{q odd, squarefree} ⌊2⁶⁴/φ(q)⌋` — at
reduced height `q ≤ 30`, with the per-element mathematics computed inside
the proved fragment: the squarefree filter is in-circuit trial division
(`urem`/comparison masks over every `d` with `d² ≤ 30`), and `φ(q)` is the
in-circuit branchless product `Π_{p∣q}(p−1)` over the fixed odd-prime list,
exactly the goldbach certificate's fast totient for squarefree arguments.
`#print axioms referenceSum_eq` reports only `propext`, and
`emit-squarefree-mertens-cert-c` emits the computation for CompCert. All
three certificates run under CompCert in the acceptance suite.

### Compiling the ternary-goldbach development itself

The hybrid pipeline compiles the actual project: every generated C
translation unit of the ternary-goldbach `Math` package — all 340
`TernaryGoldbach` modules, including the quarantined `native_decide`
certificate leaves and the compact native-input tables — and all 2,273
units of the full package compile to CompCert objects with **zero
rejections**, using only the four named ABI-preserving flexible-array
rewrites. Results, revisions, and the reproduction command
(`scripts/compile-ir-tree.py`, which batch-compiles any `.lake/build/ir`
tree) are recorded in
[compatibility/ternary-goldbach-2026-07-28.md](compatibility/ternary-goldbach-2026-07-28.md).

### The verified reflection bridge

`LeanCompCert/Verified/Reflect.lean` closes the Lean-to-C bridge for the
bounded-fold subset: a deep-embedded register program (`Reflect.Program`)
whose denotation is plain Lean `Nat` arithmetic and whose compilation
targets the proved `StraightInstruction` fragment, with a once-and-for-all
structural theorem (`Program.evalCC_compile`, axioms: `propext`,
`Quot.sound`) that the compiled CCIR trace computes exactly the
denotation. Its operation set — the ten unsigned binary operations, the
six comparisons (compiled through the validator's `u8` discipline and a
proved cast), `mov`, literals, and a first-class loop index — was chosen
from a complete operation inventory of the ternary-goldbach development's
1,371 `native_decide` atoms, recorded in
[compatibility/ternary-goldbach-ops-2026-07-28.md](compatibility/ternary-goldbach-ops-2026-07-28.md):
it is scalar-complete for the integer fixed-point certificate families.

`Testing/ReflectedCertificate.lean` re-derives the §14.1 squarefree
Mertens certificate through the bridge: `verified_decide`'s kernel work is
now evaluating `Program.denote` — an ordinary Lean fold — rather than
walking the CCIR model, while the CCIR trace, the production lowering, and
the generated-C model stay connected by the structural theorems alone. The
same computation compiles and runs under CompCert via
`emit-reflected-cert-c`.

### Status against the production certificates

The roadmap that grew out of this gap analysis is now implemented
([ROADMAP.md](ROADMAP.md)): scale-free packaging, the complete wide
arithmetic and equivalence libraries, rolled loops, the array machine
with its proved sieve sweep, and the Clight bridge through to a
Coq-kernel semantics theorem. What migration of the 1,371-atom suite
needs from the goldbach side — chunked certificate statements and the
consumer-side Mathlib equivalence lemmas — is described in Tutorial 3
and the compatibility reports.

## Compatibility results (2026-07-28)

### Prominent-project compilation

Unchanged upstream Lean sources at pinned revisions were tested on AArch64
Linux with CompCert 3.17. A successful translation-unit result means Lean
emitted C, the normalizer made only its named mechanical ABI-preserving
rewrites, and CompCert compiled the result to an AArch64 object. It does not
mean every module or dependency in the upstream repository was compiled by
CompCert.

| Project | Pinned revision | Tested source | Result |
|---|---|---|---|
| Lean/Lake 4.32.1 | `f054605aea4b` | `LakeMain.lean` | CompCert object linked and `--version` differentially matched |
| Batteries 4.32.0 | `023ce7d62a05` | `Batteries/Data/HashMap/Basic.lean` | CompCert object produced |
| Aesop 4.32.0 | `a7dbf0c63b69` | `Aesop/Search/Main.lean` | CompCert object produced |
| mathlib4 4.32.1 | `520045ab14e2` | `Mathlib/Tactic/NormNum/Core.lean` | CompCert object produced |
| doc-gen4 4.32.1 | `4df39adbbe5f` | `Main.lean` | CompCert object linked and `--help` differentially matched |

The doc-gen4 check replaced the conventional `Main.c.o.export` entry in Lake's
recorded response file with the CompCert-built `Main.o` plus the conventional
atomics adapter; all other imported objects remained those from the normal Lake
build, and the mixed and upstream executables produced byte-identical output.

These results show that sizable real Lean-generated application modules are
accepted by CompCert and that CompCert objects interoperate with ordinary Lake
objects at the tested ABI boundary. They do not establish whole-repository
CompCert builds: imported project modules remained conventionally compiled,
doc-gen4's C/C++/SQLite/Markdown dependencies remained external, and
whole-package replacement needs a Lake facet that maps every module object into
the existing link graph.

### `native_decide` substitution

Every reducible `native_decide` site in the pinned Lean/Lake 4.32.1 source (4
of 4) has an axiom-free replacement using `verified_decide` or constructor case
splitting; reproducers and a `patch --dry-run`-verified patch are in
`compatibility/native-decide/`. mathlib's closed arithmetic proposition is also
handled.

The 17 remaining mathlib occurrences are exact `reprStr`/`Format.pretty` String
snapshots whose kernel evaluation reaches a private `partial def`
(`Std.Format.be`) with no reducible body or specification theorem. No
tactic-only change can construct an axiom-free proof there; resolving them
requires refactoring the pretty-printer into a total logical function or
proving a specification for the partial renderer.
`compatibility/native-decide/MathlibOpaque.expected-failure.lean` locks in this
safety property. One further mathlib site is a linter fixture that exists to
test the `native_decide` warning itself and is deliberately left in place.

An axiom audit (`compatibility/native-decide/TacticSyntax.lean`) confirms the
replacement proofs depend only on `propext`, `Classical.choice`, and
`Quot.sound` — there is no native evaluation axiom. All five pinned projects
(Lean/Lake, mathlib4, Batteries, Aesop, doc-gen4) build, and the complete
executable compatibility matrix passes:

```console
./scripts/test-native-decide-compat.sh
```

## Authoring a certificate

The supported workflow (see `Testing/FixedPointCertificate.lean` for a
complete example):

1. Write a `Verified.Reflect.Program`: registers, a loop body over the
   index, an epilogue, an output register. Comparisons yield `0`/`1`;
   filters and early exits are comparison masks (the poison-flag
   discipline, proved equivalent to early-exit recursion in
   `Verified/EarlyExit.lean`); wide values are limb pairs with proved
   carry patterns (`Verified/Limb.lean`).
2. Discharge `program.WF` by `decide` — it is program-sized.
3. Package with `program.toComputation name hWF` — every other proof
   obligation is structural (M1).
4. Prove the specification through `toComputation_returns`: acceptance is
   exactly `program.denote = some v`, so `decide +kernel` evaluates one
   Lean-level fold. **Chunk large folds**: monolithic 10⁵⁺-element
   pipelines can exhaust the kernel (measured); split into partial sums
   combined by proved lemmas.
5. Emit with `Lower.compileProgram` and check independently under
   CompCert; the exit status is never admitted as a theorem.

The acceptance suite's axiom-audit gate (`scripts/AxiomAudit.lean`) fails
CI if any certificate acquires a native-evaluation axiom.

## Public API and versioning

The consumable surface, kept stable under semantic versioning from
`LeanCompCert.backendVersion` (currently 0.2.x — breaking changes to any
item below bump the minor version until 1.0, and the major version
after):

- `Verified.Reflect`: `Program`, `Program.denote`, `Program.compile`,
  `Program.WF`, `Program.toComputation`, `toComputation_returns`,
  `Program.counterAugment`, and the rolled emission
  (`Verified.Rolled.emitRolled`, `rolledTrace_eq_augmented`,
  `rolledResult_eq_denote`);
- `Verified.Decide`: `Computation`, `Decision`, `verified_decide`;
- `Verified.Limb`: the limb representation and its value theorems
  (`adc_val`, `sbb_val`, `lt_iff`, `mulLimbs_val`, `divModMSB_val`);
- `Verified.EarlyExit`: `foldE`, `foldP`, `foldP_accepts_iff`.

- `Lower.compileProgram` — the emission entry point for consumer
  certificates (promoted to the stable surface; the rest of `Lower.*`
  remains implementation).

Everything else under `Proof.*` and `Lower.*` is implementation:
reachable, but not covered by the stability promise.

Consumer notes (see `examples/consumer/` for a complete external
project): the C symbol for `toComputation name …` is `l_` + `name` with
dots replaced by underscores (`ABI.mangle`); certificate `Decision`
proofs use `set_option maxRecDepth 800000` with `decide +kernel`; and
compiling emitted C needs `-I<repo>/runtime/include` plus
`-I"$(lean --print-prefix)/include"`.

**Toolchain policy**: the core stays Mathlib-free; Lean-version churn in
compiler APIs is isolated behind the `LCNF/AdapterV4_32.lean` pattern —
new Lean versions add adapters rather than editing consumers.
**Consumer adapters**: Mathlib-dependent equivalence lemmas (relating
reference functions like `Nat.minFac` to package denotations) belong in
consumer projects, in the goldbach development's "proven in the
consumer" style; this package exposes the denotations they target.

## Development

```console
lake build
python3 -m unittest discover -s tests
```

Run the complete local acceptance path — including real Lean LCNF capture,
stable-view lowering, CompCert compilation, native execution, the ordinary-C
probe, and both test suites — with:

```console
./scripts/test-compcert.sh
```

The acceptance suite also builds the proof because `LeanCompCert.lean` imports
the proof module.

The fast inner loop, for iterating without CompCert or Coq installed:

```console
lake build lean-compcert-tests && ./.lake/build/bin/lean-compcert-tests
```

It runs in about two seconds and covers every worked example printed in
`docs/`, plus the adversarial cases. **[What is tested, and where](docs/testing.md)**
maps each documented claim to the test that pins it, names the mutation used to
confirm that test can actually fail, and states plainly what is *not* covered.

## Scope and honest self-description

The roadmap's milestones are implemented (see [ROADMAP.md](ROADMAP.md)
for per-milestone evidence and the precisely-stated boundaries: the
production direct-Clight semantics check covers the straight-line temp-only
fragment. Its generic Coq theorem also handles rolled loops and CompCert
pointer loads/stores; the production array AST is checked as an exact instance,
the Lean rolled/literal traces are proved equivalent, and the flat-array/
CompCert-block load/store invariant is proved. The remaining array seam is a
per-artifact refinement from the fast production-step computation to the
exact Clight loop body (plus the Lean theorem that this 100000-case denotation
is `99952`), so the final numeric array artifact does not yet have the same
unconditional `eval_funcall` theorem as a straight-line
certificate. The
Lean- and Coq-side results are tied by shared certified constants). A
complete CompCert-built runtime and strict standalone builds remain
outside scope. Lean's elaborator and kernel, Coq's kernel, and
CompCert's stated assumptions (assembler, linker, hardware) are trusted,
as in every verified-compilation stack. This project describes itself as
a Lean native backend and verified-computation package that obtains
CompCert's verified C-to-assembly guarantee, with kernel-checked
certificates and a Coq-kernel-checked Clight semantics theorem for its
certificate fragment — not as a formally verified compiler of arbitrary
Lean programs to machine code.
