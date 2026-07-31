# How a computation enters a proof

You have a theorem that needs a finite fact, and a computer establishes that
fact. **How does the computer's answer become part of the Lean proof?**

There are exactly three answers. Two are complete today and you should use
them. The third is the one people reach for first and it is the one with real
gaps — so it is documented here with those gaps named rather than glossed.

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

## Route C — attested execution

**Status: incomplete. Do not present it as finished.**

For a computation too expensive to re-run — hundreds of core-years — the run
happens once, inside a hardware-attested enclave that signs a statement naming
the algorithm, its input and its result. Lean then verifies that signature and
consumes the result through a named axiom.

The machinery that exists and works: a receipt format Lean checks
(`sparkinterval.phala-tdx-attested-run.v1`), an in-kernel SHA-256 and TDX quote
parser, P-256 verification against a pinned enclave key, and an offline gate
walking the certificate chain to Intel's root.

**What is missing, and each of these is load-bearing:**

- **The realisation premise.** `evalCC_compile` proves the compiled C computes
  the program's *denotation*. Nothing proves the denotation is the
  *mathematics*. Until that is proved for a given program, an attested run
  yields a signed number and no theorem.
- **An elimination rule.** The attested-emission relation is currently opaque:
  even a perfect receipt gives you a proposition you cannot get mathematics out
  of.
- **A pinned enclave identity** for the deployment in question, which is a
  deliberate human review step, not a build artifact.

Until those close, Route C **relocates** an assumption rather than discharging
one — and that is worth doing, since a mechanically-checkable execution
assumption beats an unexamined citation, but it must be described as what it
is.

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
Can the kernel reach it?                     → Route A
Can someone re-run it in reasonable time?    → Route B
Neither?                                     → Route C, with the gaps stated
```

Prefer A over B, and B over C. **Do not reach for attestation because it sounds
stronger** — a re-checkable answer is better evidence than a signature, because
it requires trusting nobody.

## Anti-patterns

- **`native_decide` to bridge the gap.** It admits Lean's compiler and runtime
  into the proof, which is what this package exists to avoid.
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
