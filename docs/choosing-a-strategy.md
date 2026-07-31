# Choosing a strategy for a finite computation

You have a finite mathematical claim and a `native_decide` that is too slow, or
a computation too large for the kernel. This document tells you which route to
take, what each one costs in trust, and which mistakes have actually been made
here — every trap listed below was found by a real failure, not imagined.

Start with the question most people skip.

## 0. Is it slow for the wrong reason?

**Before concluding that a computation is infeasible, check its
representation.** Three times in this project a "hopeless" computation turned
out to be cheap once the representation changed:

| case | before | after |
| --- | --- | --- |
| Helfgott A.36 bisection, 256 leaves | 13.2 GB, **unfinished at 22 min**, `native_decide` | **1.06 s, 0.64 GB, `decide +kernel`**, no axioms† |
| CH25 Lemma A.7 | modelled as unreachable | 100.2 s, 9.70 GB, `[propext]` |
| Platt zero enumeration | quoted in core-*years* | 158 s of CPU |

† **Read "no axioms" narrowly.** It compares the *same obligation* under two
mechanisms — `native_decide` admits Lean's compiler and runtime into the proof;
`decide +kernel` admits nothing — and that difference is the whole reason to
prefer the kernel. It is **not** a claim that the mathematics is proved from
nothing: the axiom-free theorem says a Boolean function returns `true` on 256
integer inputs, mentions no real numbers, and **cannot tell you whether that
predicate encodes the bound you meant**. A wrong constant yields a true,
axiom-free theorem about the wrong predicate. See
[what `#print axioms` does and does not tell you](what-is-proved.md#1b-what-print-axioms-does-and-does-not-tell-you).

The bisection case is the sharpest. It was never blocked on leaf count — 256
leaves is nothing. It was blocked on `ℚ`: the enclosure used exact rational
arithmetic and its square root was a Newton iteration that **squares the
denominator every step, three roots deep per leaf**, so the last leaf dragged
tens-of-thousands-of-bit numerators through every comparison. Moving to `2⁻²⁴`
fixed point with proved outward rounding removed the whole problem.

The Platt case was worse: the cost had been measured with a routine that
isolates **one zero at a time**, when the library also ships a whole-window
multi-evaluation entry point. Same library, same answer, 511× apart.

So: **is your cost representation, or is it mathematics?** Exact `ℚ` in a
kernel loop, structure literals where a packed `Nat` would do, and per-item
library calls where a batched one exists are the three usual answers.

## 1. The decision tree

Once you know the cost is real, pick by size and by whether anyone can re-run
it.

```
Can it be re-checked by someone who does not trust you?
├── YES, and it fits the kernel  ────────────►  decide +kernel        (best)
├── YES, but too big for the kernel  ────────►  CompCert artifact
└── NO (re-running costs months of CPU)  ────►  artifact + attestation
```

**Kernel reach, measured.** With fixed-point arithmetic the kernel scales a
clean ×4 per bisection depth level in *both* time and memory, with memory
binding first: 1.06 s / 0.64 GB at 256 leaves, 5.21 s at 1024, 19.8 s at 4096,
101.6 s / 16.6 GB at 16384. So **roughly 2·10⁴ items is the practical ceiling**
for that shape. A survey of all 143 interval-bisection sites in the ternary
Goldbach development found the deepest is depth 14 — so the entire family fits,
once the arithmetic is fixed point.

**Artifact throughput, measured.** Segmented sieves run at 59–79 ns/integer
(`ArraySegSieve`), 158 ns (`PsiSegSieve`), 367 ns (`R2SegSieve`), 2705 ns
(`CDEMAbelScan`); the bisection artifact is 177.6 ns/leaf and **flat in depth**
— 21 kB of C and a 3776-byte binary whether you ask for 2⁸ leaves or 2³¹. Its
depth-31 run (2,147,483,648 leaves) takes 381 s.

**Do not reach for attestation when re-running is cheap.** A re-checkable
answer never requires trusting its producer, so a 27-minute campaign anyone can
repeat is *stronger* evidence than a signed quote. Attestation earns its place
only where re-running is genuinely out of reach.

## 2. The CompCert route, step by step

1. **Reduce to a `Nat` family.** Restate the real-valued claim as one over
   naturals with exact integer arithmetic. This is where the mathematics is.
2. **Prove non-weakening, machine-checked.** Not a comment — a theorem. The
   strongest form is two-sided: forward (`family → statement`), a bound on how
   much stronger the reduction is, and the converse given that slack. See
   `CDEMAbelIncrementReduction`, where the reduction is shown to be at most
   `1.7·10⁻⁹` stronger against a budget of `3.2·10⁻⁴`.
3. **Implement as an `AProgram`** of the proved fragment. `Ports/R2SegSieve.lean`
   is the richest model — a segmented sieve producing per-cell factorization
   data and draining a stream through a fixed-point log phase.
4. **Land on `AProgram.evalCC_compile`** (`Verified/ArrayBridge.lean`), proved
   at `[propext, Quot.sound]`. This is the bridge from the Lean-modelled
   program to the emitted C.
5. **Write an independent C oracle** — genuinely independent, not a
   transliteration of the Lean. See §4 for why this is not optional.
6. **Check bit-for-bit under both `ccomp` and `gcc`**, at production
   parameters if the runtime allows, on *every* output slot rather than the
   headline number.
7. **Register in `check-native`** and add the new theorems to
   `scripts/AxiomAudit.lean`.

Available proved primitives: `LogFixed` (`logFix_bracket`, an exact integer
bracket), `ExpFixed` (`expFix_bracket`, unconditional; `P ≤ 30` in pure u64),
`AddWide` (two-limb accumulators), `MulWide`, `Dyadic`/`DyadicBisect` (outward
square root, stated *squared* so it pins the value without naming a real).

## 3. The trust ladder

Cheapest trust first. Prefer the highest row you can reach.

| route | axioms | who must be trusted |
| --- | --- | --- |
| `decide` / `decide +kernel` | `[propext]` | the Lean kernel |
| CompCert artifact | `[propext, Quot.sound]` for the bridge | + CompCert's Coq proof; + assembler and linker, which its theorem does **not** cover |
| attested execution | + one named axiom | + TDX, the quote verifier, the hardware |
| `native_decide` | `<name>._native.native_decide.ax_1_1` | + the Lean compiler and runtime |

Note the last row's shape: since Lean 4.32 `native_decide` no longer emits
`Lean.ofReduceBool`, so grep for **both** forms when auditing.

A note on LeanCert's `interval_decide`: by default it is `native_decide`
underneath — a measured example carries
`LogTables.log_7_gt._native.native_decide.ax_1_10`. Since v4.32.2 there is a
kernel mode, `interval_decide (trust := kernel)` or
`set_option leancert.trust "kernel"`, which lands on the base trio. For **point
inequalities** kernel mode costs the same as native; the crossover is around
10⁴ finite-sum terms. Use the kernel mode.

## 4. Traps

Every one of these produced a wrong or vacuous result here.

### Soundness

- **`Nat` subtraction truncates at zero.** `a - b` where `b > a` is `0`, not
  negative. Either prove the ordering or restructure so the subtraction cannot
  underflow. In `CDEMAbelScan` truncation was deliberately *used*, with both
  one-sided differences kept separately — that is fine, but it must be a
  decision, not an accident.
- **Rounding direction is not uniform within a single claim.** For an upper
  bound on `dPos/k − dNeg/k`, the positive term needs `1/k` over-estimated
  (`⌈W/k⌉`) and the negative term needs it **under**-estimated (`⌊W/k⌋`). The
  floor is the safe one on a negative term. Getting this backwards produces a
  reduction that looks conservative and is not.
- **Ask which direction is dangerous, for every inequality.** `divHi` at a zero
  divisor returns `0`, which makes an enclosure's upper endpoint *tighter* than
  the truth — the one direction that lets a false claim pass. The fix is to
  check `0 < den.lo` rather than to reason that the divisor is nonzero.
- **Interval endpoints: `x <` versus `x ≤`.** This produced a **false axiom**
  in the ternary Goldbach development — a Platt μ-sum bound asserted on a
  closed interval whose right endpoint exceeds the majorant by relative
  `8·10⁻⁶`. Two clauses of the `Nat` family made it visible; a single-clause
  statement would have hidden it.
- **A window threshold must be evaluated where the majorant is worst.** Testing
  at `√hi` when the family's majorant is `1/(2√(hi+1))` is anti-conservative by
  one integer step.
- **A chain can exit 0 over a wider range than it legitimately certifies.**
  "0 violations" means the check passed, not that the check had enough slack.
  Establish coverage from the rounding budget, not from a green run.
- **A chain driver that checks only the violation count is worthless.** Each
  window must also match the previous window's carry-out; otherwise a window
  seeded with the wrong carry-in still exits 0 and the chain proves nothing.
  Verify by deliberately corrupting a carry-in and confirming rejection.
- **Uninhabited contracts.** A structure with no constructor anywhere makes
  every downstream theorem conditional on something nobody can supply — and it
  looks perfect under `#print axioms`. Exhibit a term, or say you could not.
- **A passing-only agreement check cannot distinguish a correct encoding from
  one that always returns zero.** Test against a configuration that *fails*
  too.

### Mechanical

- **Emitting a large table as literals stack-overflows `ccomp`.** 27,421
  prime-power entries became 82,277 init statements and 5.3 MB of C: `gcc`
  compiled it in 22 s, `ccomp` overflowed and was still climbing past 27 GB
  with an unlimited stack. Generating the entries in the loop cost 8
  instructions and halved the init block, after which `ccomp -O2` compiled the
  production artifact in 104 s.
- **Instruction order inside a helper can be load-bearing.** A `muxBody` that
  wrote `dst` before reading `y` silently became `(1−gate)²` for every
  conditional update whose target was its own source, and the artifact returned
  *confident garbage* — 46 violations with a value off by four orders of
  magnitude. The independent oracle caught it on the first comparison; nothing
  else would have.
- **`AProgram.denote` will not always reduce in the kernel.** It threads the
  register file as a closure chain, one link per write, so reads are
  `O(writes so far)` and the loop is quadratic. A body writing 378 registers
  over 351 iterations is ~1.3·10⁵ links deep and defeats the interpreter. When
  this happens, say so and compensate by running the oracle at production
  parameters.
- **Peak RSS is not reclaimed between `decide`s in one process** — only across
  compilation-unit boundaries. A module accumulating many certificates is a
  memory bomb no matter how cheap each one is. Sharding one 88 GB unit into 16
  gave 12.8 GB each with the mathematics unchanged.
- **Check the accumulator's rounding budget before spending discovery hours.**
  The budget is subtracted from the threshold, so it must stay far below the
  majorant across the whole range. One campaign lost 3,204 integers to this;
  a sibling campaign, checked first, turned out to need no change at all.
- **`grep sorry` overcounts.** Docstrings that assert the *absence* of sorries
  contain the word. Exclude backticked occurrences before believing a count.

## 5. Worked examples in this repo

| what | where | route |
| --- | --- | --- |
| bisection enclosure, 256 leaves | `Ports/A36Bisect.lean` | `decide +kernel`, no axioms |
| segmented Möbius / Mertens | `Ports/ArraySegSieve.lean` | artifact |
| ψ residue | `Ports/PsiSegSieve.lean` | artifact |
| factorisation sieve, `R₂*` | `Ports/R2SegSieve.lean` | artifact |
| Abel summation over a μ table | `Ports/CDEMAbelScan.lean` | artifact, oracle at production scale |
| fixed-point exponential | `Ports/ExpFixPort.lean` | artifact |

See also `tutorial-3-replacing-native-decide.md` for the equivalence
architecture, `use-case-2-verified-artifact.md` for a single worked artifact,
and `tutorial-5-loops-and-scale.md` for rolled emission and kernel budgets.
