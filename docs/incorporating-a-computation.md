# How a computation enters a proof

You have a theorem that needs a finite fact, and a computer establishes that
fact. **How does the computer's answer become part of the Lean proof?**

There are exactly three answers, and you should try them in this order. The
first two are complete and assume nothing. The third is new: this package now
supplies **one** opt-in bridge that admits an execution into a proof, and using
it puts a named axiom in your `#print axioms` — which is exactly the point,
because admitting an execution should be visible and deliberate.

The single most important thing on this page: **for any computation someone can
re-run, you do not need to get the run *into* Lean at all.** The complete,
honest method is a conditional theorem plus a reproducible artifact. That is
not a workaround; it is the better shape, because it makes the obligation
explicit and lets anyone discharge it themselves.

## Route A — small enough for the kernel

**Status: complete. Use it whenever it reaches.**

```
real-valued claim
  │  proved reduction, in Lean
  ▼
Nat family (exact integer arithmetic)
  │  decide +kernel
  ▼
theorem, base trio or better
```

Nothing external is involved. `Ports/A36Bisect.lean` is the worked example: 256
leaves, 1.06 s, and the Lean proof uses no axioms.

**What you must supply**: the reduction, *proved not to weaken the claim*. That
is the mathematics and it is per-statement. See the two-sided pattern in §
"What you owe" of [writing a program](writing-a-program.md).

**Reach**: roughly 2·10⁴ items with fixed-point arithmetic. Check first whether
your computation is slow for a *representational* reason — exact `ℚ` in a
kernel loop has three times looked like an impossibility and been a
representation bug. See [choosing a strategy](choosing-a-strategy.md).

## Route B — too big for the kernel, but re-checkable

**Status: complete. This is the default for everything the kernel cannot
reach.**

The insight is to stop trying to smuggle the run into Lean. State the theorem
*conditionally* on the computation's verdict, and ship the artifact that
discharges it:

```lean
/-- The real-valued claim, given the finite check. -/
theorem myClaim_of_check (h : MyNatFamily) :
    ∀ x : ℝ, a ≤ x → x ≤ b → |f x| ≤ g x :=
  myClaim_of_natFamily h        -- the proved reduction

/-- What the artifact establishes when it exits 0. -/
def MyNatFamily : Prop := ∀ n, lo ≤ n → n ≤ hi → checkAt n = true
```

The consumer's obligation is now explicit: run the artifact, observe exit 0,
and supply `MyNatFamily`. **Nothing is hidden.** A reader who does not trust
you runs it themselves — and an answer anyone can re-derive never required
trusting its producer in the first place.

This is already the idiom in the consuming project: theorems ending
`…_of_stronger`, `…_of_inputs`, `…_of_source` take the finite fact as an
argument, with a thin "historical-provider" wrapper supplying it at the
boundary. That structure is what made a false endpoint cheap to fix when one
was found — the mathematics was parameterised over the finite claim rather than
entangled with it.

**What you must supply**, all of which this package's tooling produces:

1. the proved reduction (as in Route A);
2. the program, with `…_wf` and `…_compiled` against
   `AProgram.evalCC_compile`;
3. the artifact, plus the exact command to reproduce it and the expected
   output;
4. an **independently written oracle** and its agreement, because nothing above
   checks that your program encodes your mathematics — see below.

**What this does *not* prove**, stated plainly: that any particular run
happened. That is an empirical fact about a machine, and the conditional form
is honest precisely because it does not pretend otherwise.

## Route C — admit the execution, through one opt-in axiom

**Status: usable. It costs you one named axiom per admitted execution. Reach
for it only when re-running is genuinely out of reach.**

For a computation nobody can repeat in reasonable time — hundreds of core-years,
or two hundred shards that each took a day — the run happens **out of band**,
once, and every later build reads a record of it. The bridge lives in
`LeanCompCert/Trusted/`, and importing it is how you opt in:

```lean
import LeanCompCert.Trusted.EvidencedDecide

theorem shard7_ran : shard7Program.denote = some 1928 := by evidenced_decide
```

```
$ lake env lean -e '#print axioms shard7_ran'
'shard7_ran' depends on axioms: [propext, Classical.choice, Quot.sound,
                                 shard7_ran._evidenced.run.ax]
```

**One entry, named after the use site, for this one admitted execution.** Admit
two hundred and thirty shards and you get two hundred and thirty entries,
greppable and countable, each of type `LeanCompCert.Trusted.EvidencedRun` — the
single statement they are all instances of. An axiom count that collapses a
campaign into one line is not an audit surface, so the tactic deliberately does
not produce one. This mirrors `native_decide`, which since Lean 4.32 emits
`<declaration>._native.native_decide.ax_1_1` per use site rather than a shared
`Lean.ofReduceBool`.

**What is admitted is the execution and nothing else.** The conclusion is
`p.denote = some n`. That the program computes *your mathematics* is the
encoding gap and is still yours to discharge — see
[the step none of the routes cover](#the-step-none-of-the-routes-cover). That
the compiled C computes the denotation is *proved*, by
`AProgram.evalCC_compile`, and is not part of what you are trusting.

### The evidence record, and why its shape is what it is

The axiom has two premises, both decidable and both re-checked by the kernel:
`e.challenge.program = p` — *this record is about this program* — and
`RunEvidence.verify e n = true` — *this record is coherent and answers this
claim*. `verify` is ordinary Lean the kernel evaluates. A record has two
halves:

* the **challenge** — fixed *before* the run, and therefore visible in the diff
  a reviewer reads: which program, which shard of which campaign, which artifact
  digest, which toolchain, which machine, which value the artifact must report;
* the **facts** — what a runner reported afterwards.

`verify` checks the facts against the challenge and against the claim. Be clear
about what that is worth: it is a **well-formedness and binding check, not an
authentication check**. It does not prove a run happened — the axiom is what
asserts that. What it buys is that a record cannot *drift*: evidence produced
for one program, one value, one machine, one shard or one nonce cannot be
silently reused for another. That is the realistic failure, and it is the same
stance `NativeCheck.machineIdentity` already takes about its stamp.

Each of these is a theorem, proved at the base trio, in
`LeanCompCert/Trusted/Evidence.lean`: a wrong artifact digest, a wrong value, a
wrong machine, a wrong nonce, a truncated record, an incoherent shard, and a
verdict that is not `agrees` each force `verify = false`. A wrong *program* is
refused by the other premise. A checker that can only pass is worthless, and
this project has been bitten by exactly that before.

The program binding is a separate premise rather than a clause of `verify`, and
the reason is worth recording because it is a measurement, not a preference.
Real certificate programs are **not kernel-reducible to constructor form**:
`decide (program = program) = true` is not closed by `rfl` for
`Testing.ArraySegCertificate.program` even at `maxRecDepth 1000000`. A clause
that cannot reduce is a clause that always fails. Stated as an equation instead,
the kernel discharges it by unfolding the evidence constant and taking two
projections — so the binding became both *cheaper* (O(1) rather than O(program))
and *available*, on programs the clause could not evaluate at all.

### Three ways evidence arrives — and the difference is visible in the record

Same obligation, same axiom, same proof term. Only the record differs.

| mode | what it is | build cost | when |
| --- | --- | --- | --- |
| `cache` | a stamp left by an earlier passing run **on this machine, with this CompCert install** | stamp comparison | the routine build |
| `run` | the artifact executed **now**, against a fresh challenge nonce | the artifact's full runtime | when you want to *know* |
| `attest` | a signed attestation of a run performed elsewhere | stamp comparison | the expense was paid once, by someone else |

**`run` is what you do when you want to know; `cache` and `attest` are what
builds do.**

A cached stamp is a *record that a run happened*, which is not nothing — but on
its own it cannot be told apart from a fresh run. What distinguishes them is a
**challenge nonce chosen before the run and echoed by the artifact**. The nonce
is embedded in the compiled C, so the artifact digest is nonce-dependent and no
earlier stamp can match a new nonce; the record echoes the nonce it was
challenged with; and `verify` requires the echo to equal the nonce the claim
quotes. Evidence carrying nonce `A` therefore cannot answer a claim quoting
nonce `B` — a stale cache **fails** rather than silently passing. In the other
direction, a `cache` record has no nonce at all and one that claims to have
echoed a nonce is refused, so `cache` cannot masquerade as `run`.

`attest` is **not implemented**, and says so: `RunEvidence.verify` returns
`false` for the `tdxAttested` constructor, always, and
`LeanCompCert.Trusted.verify_tdxAttested` is that fact as a theorem. The pieces
needed to close it already exist in the `gpu_prover` deployment — in-kernel
SHA-256, v4 quote parsing down to `mr_config_id` and `report_data`, P-256
against a pinned enclave key, and an offline gate walking the certificate chain
to Intel's root. Wiring them in is **one new case of `verify`, and no new
axiom**: that is what the closed `RunEvidence` inductive is for. A constructor
that honestly refuses beats a stub that passes.

### Which mode you get is a config decision, not a Lean decision

The Lean source states the obligation. A configuration file states how it is
resolved:

```
# leancompcert-evidence.cfg — checked in
policy       = attest, cache        # use attestation if available
evidence-dir = evidence
ledger       = evidence/ledger.log
producer     = ./scripts/produce-evidence.sh
require-live-machine = true
```

```
# leancompcert-evidence.local.cfg — not checked in
policy = cache, run                 # the stamp if a run exists, else run it
```

Two consequences worth stating:

* **Changing the policy does not change the proof term.** The use site
  elaborates to `ax p n evidence h` whatever the policy was; only the
  *definition* of the evidence constant differs. So a developer iterating on
  the cache and a release build consuming attestations produce the *same*
  theorem, and the difference is visible in the record and in the ledger rather
  than buried in a proof.
* **A config file can never assert a result.** It says where to *get* evidence;
  `verify` still checks that what arrived answers the claim.

There is no built-in default. With no configuration file the tactic **fails
closed** rather than quietly selecting the weakest option. Failures are loud and
distinguishable: *no evidence available* and *evidence present but stale* are
recoverable by producing evidence again; *evidence present but invalid* is not,
and means something is actually wrong.

Every resolution is appended to the ledger, so which regime satisfied which
obligation is recorded rather than inferred.

### Build time does not depend on how long the computation took

This is the property that decides whether any of it gets used. A twenty-core-hour
shard and a one-second shard cost the **same** at build time: a stamp check. The
computation happens once, out of band; every later build verifies a record.

Measured, on the `mobius-seg` certificate: **1.86 s in the tactic and 1.38 s in
the kernel**, per admitted execution. The same file with the obligation replaced
by `sorry` elaborates in 0.63 s, so ~3.2 s is the tactic's own cost. It is the
same 3.2 s for `copyIdxProgram`, a three-instruction program — the cost does not
move with the program, and it does not move with how long the artifact ran.

That is why the record carries a digest, a verdict and an identity and **never a
trace or a transcript**. `verify` is a fixed handful of string and integer
comparisons plus one structural comparison of the `AProgram` — bounded by the
program's *source* size, and independent of its `loopCount`. Any evidence design
whose checking scales with the work done would defeat the purpose, which is why
none of the three modes has one.

### What this buys over `native_decide`, honestly

**Better.** `native_decide` admits Lean's *unverified* compiler and runtime,
opaquely. This admits CompCert's machine-checked semantic-preservation proof,
plus the assembler and the linker, through a named axiom whose premise is an
**inspectable evidence record** the kernel re-checks. Strictly smaller, and far
better understood.

**Not free.** The computation has to be expressible in the proved fragment — no
recursion, no early exit, a fixed trip count. That is real work and it does not
always succeed. In the consuming ternary-Goldbach project 268 `native_decide`
axioms remain, and a measurement showed that one 220-atom family does *not*
convert by the obvious route: `outward` truncates only at node boundaries, while
series and Newton steps build large rationals *inside* a node, so a
whole-way-through fixed-point rewrite is needed first. Do not present the
replacement as mechanical.

**Same speed.** The reason people reach for `native_decide` is not that they
want to trust a compiler; it is that they cannot afford the kernel redoing the
work on every build. A single `native_decide` in `AppendixACertWide` measures
1608 s, and converting the remaining 268 to in-kernel `decide` was measured at
109 core-hours. Under this design both become stamp checks.

### Sharding

A computation too big for one run is split into independently runnable shards,
each with its own evidence, possibly produced on different machines and in
different modes — attest the expensive shards, cache the cheap ones. That
mixture is normal.

A record names its shard: campaign, index, count, the loop range it covers, and
digests of the carry it was seeded with and the carry it hands on. So shard 7's
evidence cannot be presented for shard 8, and a composition theorem — *if every
shard's verdict holds, and the carries link, and the shards cover the range,
then the whole claim holds* — has well-formed, individually verifiable objects
to quantify over. Per-use axioms then give one `#print axioms` entry per shard,
which is the right granularity: a reader sees exactly how many independent
executions were admitted.

## Where the loop closes, and where it does not

**The `LeanCompCert` library contains zero axioms, and still does.** Nothing
in it imports `LeanCompCert/Trusted/`, so a consumer who does not ask for the
bridge gets `[propext, Classical.choice, Quot.sound]` from every certificate,
exactly as before. The bridge is a separate library you import on purpose.

Inside `LeanCompCert` itself, the interface to run the calculations is
`check-native`, and its own docstring is explicit about what it is not:

> The cross-check is corroboration, never a premise: the theorems are
> established by `verified_decide` in the kernel, and **nothing here feeds back
> into Lean's proof state.**

So `check-native` catches a mismatch between what your program means and what
the artifact does. It does not, and is not meant to, give you a theorem — that
is `LeanCompCert/Trusted/`'s job, and it is deliberately a different import
with a visible cost.

Step by step, for the artifact route:

| step | closed inside leancompcert? | by what |
| --- | --- | --- |
| real claim → `Nat` family | **yes**, if you prove the reduction | ordinary Lean proof |
| `Nat` family → program's denotation | **NO** | nothing — see the next section |
| denotation → compiled C | **yes** | `AProgram.evalCC_compile` |
| C → assembly | outside Lean | CompCert's Coq proof |
| assembly → bytes | outside Lean | assembler and linker, trusted |
| "it ran and returned 0" | **only if you opt in** | `LeanCompCert/Trusted/`, one named axiom per use site |

**Two gaps remain inside this package**, and they are different in kind:

1. **The encoding gap** — that the program computes the family. Dischargeable
   in the kernel for small programs; for large ones only empirically, via an
   independent oracle. See the next section. **Nothing in Route C closes this**,
   and the axiom's docstring says so: it concludes `p.denote = some n`, not your
   mathematics.
2. **The execution gap** — that a run happened. **Not provable, here or
   anywhere.** It is an empirical fact about a machine.

The execution gap closes in one of two ways, and the order matters:

- **Re-run it.** The conditional theorem's hypothesis is discharged by whoever
  wants the result, outside Lean. Nothing is hidden and nobody is trusted. This
  is Route B and it remains the right default.
- **Admit it, visibly.** When re-running is genuinely out of reach, Route C
  admits the run through `LeanCompCert/Trusted/` — one statement,
  `EvidencedRun`, instantiated once per use site so that every admitted
  execution is its own line in `#print axioms`.

Why one bridge here rather than one per consumer: this package used to supply
none, on the principle that using it should add nothing to your axiom list. It
still adds nothing unless you import `LeanCompCert.Trusted`. But every consumer
that needed the step invented its own — the ternary-Goldbach project wrote
`phalaTdxAttestedEmission_sound` and `accepted_run_certificate_sound`, and
anyone else would have written a third. One well-designed axiom with an
inspectable, checked premise is better than N ad-hoc ones, and keeping it
opt-in preserves the guarantee that mattered.

## The step none of the routes cover

**Nothing above checks that your program computes your mathematics.**
`evalCC_compile` relates the program to its compiled C. The reduction relates
the mathematics to a `Nat` family. The join — *this program computes that
family* — is a separate obligation.

For small programs, discharge it in the kernel: evaluate `denote` on a small
configuration and compare against a simple reference such as trial division,
**including a configuration where the check is expected to fail**, since a
passing-only test cannot distinguish a correct encoding from one that always
returns zero.

For large programs the kernel cannot evaluate `denote` at all — the register
file is a chain of updates, so reads cost O(writes so far). Then the obligation
is discharged empirically, by an oracle written **from the specification by
someone who has not seen the encoding**, compared on every output at production
parameters. That is weaker, and the modules in that situation say so.

It is also not theoretical. Independent oracles in this project have caught: a
helper that wrote its destination before reading its source, silently squaring
a gate; an operator-precedence error where `>>>` bound tighter than `*`,
corrupting every table entry; and a test harness that derived its own
commitment from the data under test.

## Choosing

```
Can the kernel reach it?                     → Route A   (no assumption)
Can someone re-run it in reasonable time?    → Route B   (no assumption)
Neither?                                     → Route C   (one named axiom per run)
```

Prefer A over B, and B over C. **Do not reach for attestation because it sounds
stronger** — a re-checkable answer is better evidence than a signature, because
it requires trusting nobody. Route C exists for the case where re-running is
genuinely impossible, and the reason it makes you write an axiom down is so that
the reader can see you were in that case.

## Anti-patterns

- **`native_decide` to bridge the gap.** It admits Lean's unverified compiler
  and runtime into the proof, which is what this package exists to avoid. Route
  C is the replacement, and it is a real improvement in the trusted set — but it
  is not a mechanical rewrite, and pretending otherwise is its own anti-pattern.
- **Reading a Route C axiom count as "one assumption".** Each entry is one
  admitted execution. Two hundred and thirty entries means two hundred and
  thirty executions were taken on faith, and that is the number to quote.
- **Asserting the finite fact as an axiom "temporarily."** In the consuming
  project three such placeholders were introduced to unblock a build; they are
  still there, and were found by an axiom print rather than by anyone
  remembering.
- **Reporting a cached `check-native` pass as a verification.** It is stamped
  per machine and per CompCert install, so a hit means "this machine already
  ran exactly this" — but read the `0 cached, N run` split, and pass `--force`
  when producing evidence for someone else.
- **Quoting an axiom count as a trust summary.** See
  [what `#print axioms` does and does not tell you](what-is-proved.md#1b-what-print-axioms-does-and-does-not-tell-you).

## See also

- [What is proved](what-is-proved.md) — the three claims and the theorem
  statements.
- [The walkthrough](trust-walkthrough.md) — the same chain with no assumed
  vocabulary.
- [Writing a program](writing-a-program.md) — the fragment and its idioms.
