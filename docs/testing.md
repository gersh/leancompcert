# What is tested, and where

Two questions this document answers: *does every documented way of using this
package have a test*, and *would that test actually fail if the claim stopped
being true*. The second question is the one that matters, so every entry below
names the mutation that was used to check the test can fail.

Run everything with:

```console
./scripts/test-compcert.sh
```

The fast inner loop — no CompCert, no Coq, no network — is:

```console
lake build lean-compcert-tests && ./.lake/build/bin/lean-compcert-tests
```

which completes in about **two seconds**. That is deliberate: a test suite you
skip because it is slow is not a test suite. Anything expensive (compiling
certificates under CompCert, the Coq-kernel gates) lives in the acceptance
script, not the inner loop.

---

## 1. Documentation conformance

`LeanCompCertTests/Docs.lean`, Part A. Each section reproduces a document's
worked example *as printed*, so the prose cannot drift from the code without a
test failing or the file ceasing to compile.

| Document | What is pinned | Test |
| --- | --- | --- |
| `tutorial-1-first-certificate.md` | the printed program, its `WF` proof, the reference fold, the value **14950**, and the emitted symbol `l_Tutorial_sumDemo` | `testTutorial1`, plus `tutorial_certificate` / `tutorial_denote` as real theorems |
| `tutorial-2-wide-arithmetic.md` | `MulWide.hl` (`lo + 2⁶⁴·hi = a·b`), `Limb.adc`/`mulLimbs`/`isLt` value laws, `log2Fixed = Nat.log2`, `Dyadic` directed rounding brackets, and the documented full-scale wrap | `testTutorial2` |
| `tutorial-3-replacing-native-decide.md` | all five tabulated equivalences agree as *computations*: `foldP`/`foldE`, `isqrt = Nat.sqrt`, `spfFixed = leastFactor`, `gcdFuel = Nat.gcd` | `testTutorial3` |
| `tutorial-4-trust-chain.md` | the axiom story | the two audit gates in `test-compcert.sh` |
| `tutorial-5-loops-and-scale.md` | the rolled artifact is kilobyte-scale and contains a loop; `counterAugment` adds exactly one register and preserves the loop count | `testTutorial5` |
| `use-case-1-verified-native-decide.md` | `check-native` caching: a second run must recompile nothing | `test-compcert.sh` change-tracking assertion |
| `use-case-2-verified-artifact.md` | every certificate compiles under CompCert and runs to exit 0 | `check-native`, 14 certificates |
| `compcert-well-formedness.md` | kernel-only `CompCertWF`, proof-gated DSL serialization, generic `compile_program_correct`, and exact fixed-point `eval_funcall` | `ClightContractTest`, `ProgramClightEmitTest`, and `clight-direct-verify.py --self-test` |

## 2. What skeptics say

Part B of the same file. These objections are not hypothetical — they were
raised on the Lean Zulip thread about setups needing `native_decide`.

### "You say it will have no axioms. I don't understand how that is possible."

It is possible because the claim is a **partition**, not a blanket:

* `LeanCompCert` — zero axioms beyond `propext`, `Classical.choice`,
  `Quot.sound`. The kernel route never runs a compiler, so there is nothing to
  admit; the CompCert artifact is a cross-check and never a premise.
* `LeanCompCertTrusted` — a **separate library** carrying exactly one further
  axiom, `evidencedRun_sound`, by name.

Both halves are enforced mechanically by `test-compcert.sh`, which fails the
build if the main library acquires any axiom, or if the trusted library
acquires any axiom other than the one admitted schema. Current measured state:
286 theorems audited in the main library, and 32 audited in the trusted one of
which exactly **2** carry the admitted schema.

*Mutation:* injecting a synthetic `Lean.ofReduceBool` line into the audit log
makes the gate exit non-zero.

The scalar Lean-to-Clight acceptance instance itself uses `decide` and
`decide +kernel`, not `native_decide`.  Its Coq-side `vm_compute` creates a
kernel-checked proof and is independently mutation-tested: changing the
expected fixed-point result from `40234404` to `40234405` makes the generated
Coq check fail.

### "A checker that can only pass is worthless."

The evidence checker's refusals are **proved theorems**, not tests:
`verify_binds_value`, `verify_agrees`, `verify_binds_identity`, plus the
per-field refusals in `Trusted/Demo.lean`. `testRefusals` re-checks them as
values so a regression in the executable path is caught too.

*Mutation:* deleting the `f.answers c n` conjunct from `RunEvidence.verify` —
i.e. making the checker stop binding the value it certifies — **does not
compile**. Three theorems reject it. You cannot ship an always-accept checker;
the library will not build. This is stronger than any test.

### "Even sandboxed, a miscompilation can still make the result wrong."

Correct, and it is why the kernel route does not route the computation through
any compiler. On the artifact route the compiler is CompCert, whose
C-to-assembly correctness is machine-checked, and the C↔denotation link is
*proved* (`AProgram.evalCC_compile`), not assumed. What the axiom admits is
only that a binary ran and reported a value.

### "You just moved the build cost somewhere else."

`Trusted/ArtifactRun.lean` claims verification is a stamp comparison whose cost
is independent of how long the artifact ran. Two checks:
`testCostIndependence` bounds a single `verify`, and the acceptance suite
asserts that a **second** `check-native` run recompiles and re-runs nothing.

### "Exit 0 does not mean the right computation ran."

It does not, and a chain driver that checks only a violation count is unsound —
a wrong carry-in produces a wrong accumulator that sits comfortably under the
threshold and reports zero. `bench/moblive_chain.sh` compares all four result
slots of every link against a manifest, feeds link *i* exactly what link *i−1*
printed, and requires the first link's count to be the three known non-defects.

## 3. The anti-conservatism regression

The single most important test in the file, because the bug it guards was
invisible to every passing run.

The windowed `plattstrong` / `platt211` epilogues sampled their majorant at
`hi` when the family binds at `hi + 1`, making the threshold *larger* by a
relative `1/(2·hi)` — a test weaker than the family it certifies, i.e. exactly
the direction that lets a false claim pass. A too-large threshold only ever
makes runs pass, so no amount of green output would have revealed it.

`testAntiConservatism` therefore compares against the **old formula** and
requires the shipped threshold to be strictly harder, checks the `N = 0` corner
that used to collapse the threshold to zero, and pins `ceilSqrt` at the
documented exact-tie point `n = 4`.

*Mutation:* reverting `plattStrongerThreshold` to sample at `N` fails with
`plattStrongerThreshold 1000 is not sampled at n+1`.

## 4. What is *not* covered

Stated plainly, because a coverage table that hides its gaps is worse than none.

* **The encoding gap.** Every test here checks that a program computes what its
  *denotation* says. That the denotation is the mathematics you care about is a
  separate, per-certificate obligation — see the "What is not proved here"
  section of `Ports/MobiusResidueRealisation.lean`, which closes it for the
  residue half of the per-integer Möbius program and explicitly leaves the sieve
  half (that three named registers really carry `n` and the indicators of `μ(n)`)
  as an open premise. No test in this suite can close that, and none pretends to.
* **Production-scale evaluation.** By design: the inner loop must stay at
  seconds. Full-height runs are the acceptance script's and the benchmarks' job.
* **The C pretty-printer**, on the classic path — validated by three
  independent gates rather than proved, and eliminated on the direct path.
