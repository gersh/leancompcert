# Changelog

## Unreleased

- **`interval_bisect` was never blocked on leaf count** — it was blocked on
  `ℚ`.  `MathExtras/Analysis/HelfgottThm31/C1Bound/A36Bisection.lean`'s
  `lowBranch_nonneg_mid_low_hi` is **256 leaves** and Lean's kernel still could
  not do it: 13.2 GB, unfinished at 22 minutes.  The reason is that
  `interval_bisect`'s kernel is exact rational arithmetic and
  `sqrtTight_enclose_interval` is a Newton iteration that *squares the
  denominator* every step, three roots deep, so the last leaf drags
  tens-of-thousands-of-bit numerators through every comparison.
  - **`Verified/DyadicBisect.lean`** puts the same bisection in `2⁻²⁴` fixed
    point on top of `Verified/Dyadic.lean`: a cell grid whose endpoints round
    outward (`Grid.loM_mul_le`, `Grid.le_hiM_mul`) and therefore overlap
    (`Grid.chain`), the combinatorial cover that follows (`chain_cover`), an
    outward square root (`sqrtI_lo_sq_le`, `sqrtI_lt_hi_sq`), and a **checked**
    square root (`sqrtOK_encloses`) that lets a fixed-shape program guess the
    root by any means and prove nothing about the guess.  The root's
    correctness is stated squared — `lo² ≤ m·2^p < hi²` — so it pins the value
    without naming a real number.
  - **`Ports/A36Bisect.lean`** is the certificate.  `sweep_ok`: all 256 leaves
    pass, **`decide +kernel`, 1.06 s, 0.64 GB**, and `#print axioms` reports
    *no axioms at all*.  Against 13.2 GB and unfinished, that is the result —
    and it means this family does not have to be traded for an attested
    artifact, because the kernel can simply do it.
  - **Depth, not precision, is what the enclosure needs.**  Margin at depth 8
    is `2.0668` at `p = 20` and `2.0674` at `p = 28`; the limit is interval
    dependency, not rounding.  Depth 6 fails (−0.33), depth 8 passes (+2.07) —
    which is why the source file chose 8, and why the fixed-point form needs no
    more depth than the rational one.  Nothing was tuned.
  - **The side conditions are checked, not inherited.**  `divHi` at a zero
    divisor returns `0`, which would make the enclosure's upper endpoint
    *tighter* than the truth — the one direction that can let a false claim
    pass — so the leaf checks `0 < den.lo` (`den_pos`) rather than relying on
    `2υ(υ + j) ≥ 2`.  Likewise for the differences:  `Nat`
    `Nat` subtraction truncates at zero, so `υ − 1` and `√(1+x²) − x` would be
    sound only given `υ ≥ 1` and `√(1+x²) ≥ x`.  The leaf checks the ordering
    instead — the hypothesis of `Dyadic.DInt.sub_no_truncation` — so the
    differences are exact and no side condition is inherited
    (`differences_exact`).
  - **`Ports/A36BisectProgram.lean`** is the same leaf as a 478-instruction
    fixed-shape loop body, well-formed at every depth from one proof.  It is
    checked against `leafOK` on a configuration where the certificate **fails**
    (the depth-3 grid) as well as one where it passes: a passing-only check
    cannot distinguish a correct encoding from one that always returns zero.
  - **The wall moved, it did not vanish.**  The kernel is a clean factor of
    four per level in both time and memory (1.06 s at depth 8, 101.6 s and
    16.6 GB at 14), so its reach is about 2·10⁴ leaves — which covers *every*
    uniform-depth site in the family, whose maximum depth is 14.  The artifact
    covers what is past that: 177.6 ns per leaf, 3.8 kB freestanding at every
    depth, 2³¹ leaves in 381.4 s.  `bench/results/a36_bisect.md` has the
    tables, the survey of all 143 sites, and what is *not* proved — the
    analytic step to `ℝ` (no Mathlib here) and the body/`leafOK` simulation.

- **The two-limb accumulator, and the `ψ` residue it makes runnable** — the
  one thing between the design of the previous entry and an artifact.
  `Verified/AddWide.lean` supplies the missing primitive:
  `addWide`/`subWide` over a pair of `u64` limbs, with the carry recovered by
  a **proved comparison** (`carry_bit`: for `u, v < 2⁶⁴` the truncated sum is
  below `v` exactly when the untruncated one overflowed), so no carry flag and
  no branch is needed.  `addWide_spec` is the `mod 2¹²⁸` statement,
  `sumWide_spec` the fold: a list of `u64`s whose total is below `2¹²⁸`
  accumulates *exactly*, with no hypothesis about how the carries interact.
  - **Four instructions, not six.**  `add`, `lt`, `add`, `add` — the carry
    test reads the addend, which the first instruction does not touch, so
    there is no copy and no temporary.  The one-word specializations, which
    are what the loop runs, are three each.  `Ports/AddWidePort.lean` proves
    the register file computes them (`addWideBody_denote` and friends), stated
    in the form a loop body consumes: accumulator limbs out, every other
    register untouched, under an explicit `WideRegs` separation condition.
  - **The bracket survives the machine.**  `Verified/LogAccum.lean` restates
    `logFold_bracket` over `wval (sumWide …)` — the value of the *pair of
    registers*, not of an idealized `Nat`.  The error term `2·#terms` is
    unchanged, because `logFoldWide` says the accumulation is exact rather
    than approximate.  The two side conditions are `logFix_lt`
    (`logFix S n < 2^(S+6)`, so one term is one word, and `S ≤ 58`) and a size
    bound on the total which at `S = 48` over `π*(10¹³)` terms leaves 35 bits
    of headroom.  **`S = 48`** is the choice: `45.32` is the floor the
    printed constant's margin sets, `58` the ceiling a one-word term sets, and
    at `48` the enclosure is `1.6·10⁻⁹` — one sixth of the last printed digit.
  - **A fourth loop phase.**  `Ports/PsiSegSieve.lean` is the residue as an
    `AProgram`.  A window's period is `markSteps + segLen + logSteps`: the
    accumulation phase drops the `μ` decoding entirely (nine instructions and
    a whole array plane), merges the emit-time prime-power table in by one
    cursor and one comparison, and **compacts** the test points into a stream;
    the log phase drains it, one squaring round per iteration, `S` per entry,
    the entry boundary carried by a wrapping counter rather than a division.
    `logSteps = S·streamCap` is a budget, and both ways it can be wrong — a
    window over budget, a stream left undrained — are counted as violations by
    the loop itself.  Four more guards (the prime gap, the `⌊√n⌋` step, the
    `⌊log₂ n⌋` step, the accumulator's range) mean a zero output is a
    statement about the run and not only about the mathematics.
  - **The comparisons are one word.**  A clause's right-hand side is a 70-bit
    product; both sides are shifted right by 16 first, the constants
    pre-shifted **downward on both sides** at emit time.  Passing clause 1
    certifies `(ψ(n) − n)/√n ≤ 0.79059276 + 2.3·10⁻¹⁰/√n` against a margin of
    `10⁻⁸`, for 7 instructions instead of about 40.
  - **It agrees with the oracle bit for bit.**  At `hi = 10⁶, 10⁷, 10⁸` the
    artifact's residual equals `bench/ref_psi.c`'s to the last bit
    (`D(10⁸) = −494 608 778 557 207 013`), reproducing
    `ψ(10⁶) = 999 586.597496` and `ψ(10⁸) = 99 998 242.796627`, with zero
    violations; `ccomp` and `gcc` outputs are byte-identical.  Measured
    `201.9 ns/integer` under `ccomp` at `10⁸` (`120.9` gcc), a body of 246
    instructions, and `κ = 0.1066 ns` fitted to `±2%` across the three sizes.
    At `10¹³` the computed configuration is `6.041` iterations per integer, so
    **`158 ns/integer` and `18.3 days` on one core** under `ccomp`
    (`11.3 days` gcc).  No full-scale run was started.
  - **One fragment question, closed without an extension.**  The mantissa
    reset shifts by a register, and the fragment's `shl` is total where C's is
    undefined at width ≥ 64.  The amount is provably in `[0, 62]`, so instead
    of a checked-shift instruction the emitted amount is masked with `& 63`:
    one instruction, a no-op under the invariant, and the emitted C becomes
    total rather than merely correct.  Nothing else wanted an instruction the
    fragment lacks — the two-limb add needs no carry flag, the `ln 2`
    conversion no 128-bit multiply (eleven instructions of 32-bit halves,
    because `logFix < 2⁵⁴`), the clause tests no 128-bit compare.
  - `Ports/ArraySegSieve` is **untouched**: the `mertens` artifact still
    agrees with `bench/ref_seg.c` on all seven slots (`M(10⁷) = 1037`,
    `Q(10⁷) = 6 079 291`) and `check-native --force` is 10/10.  Full numbers
    in `bench/results/psi_fold.md`.

- **A logarithm for the fragment, and the two families that need one** — two
  of the six reduced on-cone families are not integer folds: `ψ(n)` and
  `R₂*(n)` sum logarithms of primes, which the Möbius sieve does not produce.
  `Verified/LogFixed.lean` supplies the missing primitive.  `logFix S n` is
  `⌊2^S·log₂ n⌋` by repeated squaring of a 62-bit mantissa, one emitted bit
  per round, and its correctness is an **integer** statement —
  `2^logFix S n ≤ n^(2^S) < 2^(logFix S n + 2)` — because this repository has
  no Mathlib and `Real.log` cannot be written here.  That turns out to be the
  right formulation rather than a workaround: nothing is rounded, and because
  the bracket *multiplies*, the accumulation theorem is exact.
  `logFold_bracket` reads
  `2^(Σ logFix S p) ≤ (Π p)^(2^S) ≤ 2^(Σ logFix S p + 2·#terms)`, so the
  accumulated error is the literal subterm `2 * l.length` — two units in the
  last place per factor, with no hidden `ε` and no independence assumption.
  - The squaring step is exact and division-free: `sq62_eq` proves the
    32-bit half-limb circuit computes `⌊x²/2⁶²⌋` on the nose.  The
    relative-error budget, which squaring doubles, is defined by its own
    recursion `D ↦ 2D + D²/2⁶² + 9` so that the induction step is
    definitional and the quantitative claim collapses to one `decide`:
    `errB 48 = 2 533 970 701 664 099`, five ten-thousandths of a mantissa
    unit.
  - `Ports/LogFixPort.lean` is the round as a `Reflect.Program`: **21
    instructions, no division of any width**, the renormalising shift an
    `lshr` by a register.  Kernel checks tie its `denote` to `logFrac` and to
    `logFix 20 999999937 = 31 349 646`.
  - **A single 64-bit accumulator cannot carry `ψ` to `10¹³`.**  In residual
    form the family's own bound `|ψ(n) − n| ≤ √2·√n` caps `S` at 40; the
    enclosure width there is `4·π*(10¹³)/2⁴⁰ = 1.26`, i.e. `4.0·10⁻⁷` in a
    ratio the paper prints to eight decimals.  The margin behind
    `0.79059276` is at most `10⁻⁸`, which needs `S ≥ 45.32`: **one word is
    short by a factor of 40**, and `ψ` requires 128-bit accumulation (71 bits
    at `S = 48`, so two words and a carry).  `R₂*` is the opposite case — one
    word at `S = 24` sits forty times inside its margin, and its obstruction
    is that `Λ∗Λ` is a Dirichlet convolution needing a factorisation sieve,
    not a logarithm.  Full arithmetic, the prime-power treatment, and the
    extrapolated cost (`138 ns/integer`, 16 days at `10¹³`; `1.2 hours` for
    `R₂*`) are in `bench/results/psi_fold.md`; `bench/ref_psi.c` is the
    oracle and the speed line, reproducing `ψ(10⁶) = 999 586.597496` and
    `ψ(10⁸) = 99 998 242.796627`.
  - `Ports/ArraySegSieve.lean` is untouched, so the `mertens` artifact still
    agrees with `bench/ref_seg.c` slot for slot on all seven slots and
    `check-native` still passes.

- **The reduced cite families, computed** — the one-shot `[0, L)` Möbius
  sieve of `Ports/ArrayMobius.lean` needs the whole range resident, so `10¹²`
  would be 24 TB.  `Ports/ArraySegSieve.lean` is its offset, multi-window
  successor: cell `i` stands for `lo + s·L + i`, one `AProgram` walks
  `segCount` windows, and memory stays `3L` cells however long the walk.  The
  first multiple of `p` inside a window is one `urem` when the prime cursor
  advances; the accumulation phase zeroes the two cells it has just read, so
  no clear pass is needed and the bridge's zero-filled initial memory is
  exactly the state every window wants.  Measured at `lo = 10¹⁰`: `16.9 MB`
  resident against `1.56 GB` for the one-shot form, and faster.
  - Two residue blocks ride on the sieve.  `mertensResidue` carries
    `M(n) = Σ μ(m)`, `Q(n) = Σ |μ(m)|` and the CDEM fixed-point discrepancy
    `G(n) = Q(n)·2³⁶ − ⌊(6/π²)·2³⁶⌋·n` with their running extrema — the
    residues of `mertensM_hurst_sqrt` and of the CDEM reproducible squarefree
    head, on **one** pass.  `mobiusOverNResidue` carries
    `T(n) = Σ μ(m)·round(2⁶²/m)` — the residue of Platt's (2.11) and of
    Platt's stronger rigorously-computed range.
  - Every real-valued majorant is compared once per artifact, in the
    epilogue, against an exact integer threshold computed in Lean: `Nat.sqrt`
    of a rational cross-multiplication, and a Machin computation of `π` in
    integer arithmetic for `⌊(6/π²)·2³⁶⌋ = 41 776 432 333`.  No `√` and no
    `π` appears in the artifact; the loop body only adds and compares machine
    words.
  - `segProgram_wf` proves well-formedness at every `(lo, L, segCount)` and
    either residue — by a `Bool` mirror that reduces definitionally, so the
    proof is `rfl` and does not grow with the body.
    `mertensProgram_compiled` / `mobiusProgram_compiled` instantiate
    `AProgram.evalCC_compile`.  Base trio.
  - Corroboration: kernel evaluation against trial division at `[1, 24]`;
    slot-for-slot agreement with `bench/ref_seg.c` at `10⁸`, where
    `M(10⁸) = 1928` and `Q(10⁸) = 60 792 694`, and at `lo = 10¹⁰`;
    `bench/seg_chain.sh` walking a geometric window schedule with zero
    violations for all four families over the initial stretch.  Registered as
    the `mobius-seg` native certificate.
  - Cost, and what is still out of reach, in
    `bench/results/array_seg_folds.md`: `68 ns` per integer under CompCert,
    so `7.7·10⁹` is 8.6 minutes, `10¹²` is 19.7 hours and `10¹⁶` is 25
    core-years (embarrassingly parallel, with no serial carry dependency).
    Two of the six reduced families — `ch25_lemma_9_2_psi` and
    `ramare_zuniga_lemma_6_2` — are **not** integer folds: their summands are
    logarithms of primes, and they are not implemented.

- **The build-time wall removed: the artifact no longer carries a prime
  table, and lowering no longer recurses per instruction.**  Two independent
  ceilings capped `hi` well below every target, and both are gone.
  - `MemFragment.lowerMSequence` and `Proof.lowerSequence` built their result
    on the way *out* of the recursion, keeping one interpreter frame alive per
    instruction.  Emission runs in the Lean interpreter, whose recursion guard
    fires at about ten thousand frames, so a `plattstrong` chain died with
    `deep recursion was detected at 'interpreter'` at `hi = 1.95·10⁸` — forty
    times below the `7.7·10⁹` target.  Both are now accumulator-passing and
    tail-recursive; the two equations of the naive definition are recovered as
    `lowerMSequence_nil`/`_cons` (and the `lowerSequence` pair), so
    `lowerMSequence_correct` and everything around it is unchanged.  `2·10⁸`
    went from "deep recursion" to 1.15 s; `7·10⁹` emits in 17.7 s.
  - The prime table was written by the init block, three instructions per
    prime: 235 497 statements at `10¹²`, where `ccomp -O2` segfaulted at the
    default stack and reached **30.5 GB** with an unlimited one.  The program
    now **computes** the table: `⌈√hi / L⌉` leading root windows sweep
    `[1, rootCount·L]` with the same instructions, the mark cursor stopping at
    `π(⌊√(rootCount·L)⌋)` and the accumulation pass appending `n` to the table
    exactly when its cell was never marked and `2 ≤ n ≤ ⌊√hi⌋` — which at that
    size says precisely "prime, above every bootstrap prime".  What the init
    block still spells out is `π(⌊√L⌋)` primes, a function of the window size
    and not of the range: the `10¹⁰` and `10¹²` artifacts are the *same*
    45 KB of C, `ccomp -O2` takes either in 0.06 s at 24 MB, and the
    `10¹⁶`-scale one is 235 KB, `ccomp` 0.53 s.
  - `mertensLiveResidue` removes the window-schedule weakening.  `⌊√n⌋` rises
    by at most one per integer, so it is a register and three instructions;
    each majorant is `α√n`, so `⌊α·⌊√n⌋⌋` is a multiply and a shift, and
    testing all four clauses per integer makes the four running extrema
    unnecessary — 31 instructions against 27.  One artifact over
    `[9243, 100 009 242]`, a range ratio of 10 817, reports 0 violations where
    the windowed mode on that same window reports 4.  The extremum residue is
    kept: only it can be run with a zero carry-in in any order and reconciled
    afterwards, which is what makes the `10¹⁶` pass embarrassingly parallel.
  - Measured cost of all of it, at `lo = 10¹⁰` over `10⁸` integers: 5.08 s →
    5.36 s (gcc) and 6.56 s → 6.65 s (ccomp) for the root sieve, 5.40 s /
    6.81 s with per-integer thresholds — **6% and 4%** for removing a wall
    that no verified compiler on this machine could get past.  The cost table
    is otherwise unchanged: `7.7·10⁹` is 9.0 minutes, `10¹²` is 20.4 hours,
    `10¹⁶` is 24.1 core-years.
  - With both walls gone, `bench/seg_chain.sh plattstrong 10000 7727000000
    1.02 200 ccomp` **runs to completion**: 663 windows, 0 violations,
    `[10001, 7 727 000 000]`, 2 h 23 min on one core, every artifact compiled
    by CompCert 3.17.  A second chain covers `[4, 10001]`.  That is the finite
    content of `residual_platt_stronger_range` computed end to end through the
    verified-compilation path.
  - One corner found and fixed on the way: at `segLen ≤ 3` *and* `hi ≤ 15` the
    root sweep is at most three integers, the bootstrap prime list came out
    empty, and the window-start reset — which installs the literal `2` before
    the cursor-exhausted test can intervene — marked with a prime the table did
    not contain and left a `0` for the main phase to `urem` by.  `denote` is
    `none` there so no theorem was affected, but the artifact returned a wrong
    number quietly.  `Cfg.ofRange` now takes `max (⌊√rootLen⌋) 2`, and
    `bench/seg_sweep.sh` checks 98 `(lo, segLen, segCount)` configurations
    against `bench/ref_seg.c` so the corner stays checked.

- **Verified multi-precision modular arithmetic** — the binding
  obstruction across the ternary-Goldbach corpus is gone.  The fragment's
  only division is `udiv`/`urem` at 64 ÷ 64 → 64, so `x·y mod N` for a
  ~90-bit `N` (a 128 ÷ 64 division) was inexpressible.  Montgomery
  reduction needs **no division at all**:
  - `Verified/Montgomery.lean` — the algebra over `Nat`: exactness of the
    Montgomery shift (`redcStep_mul`, the reduction-side analogue of
    `MulWide.hl_spec`), `montMul_spec`, cancellation of `Bˢ` modulo an odd
    modulus, square-and-multiply in the Montgomery domain, and the
    end-to-end `montExp_spec : montExp … = a ^ e % N`.
  - `Verified/Mont2.lean` — its two-limb realization in the fragment's own
    instruction set (`montMul2_val`), plus division-free entry into the
    domain by doubling (`dblIter_val`).  Every machine form is `+`, `-`,
    `*`, `&`, `<<`, `>>` and the proved `<`; the emitted C contains zero
    divisions.
  - `Verified/InstrBlock.lean`, `Verified/Straight.lean` — total
    straight-line block layers, so a 30 000-instruction body is reasoned
    about by composition, never by unfolding.
  - `Ports/TGProth.lean`, `Testing/ProthCertificate.lean` — stage (b) of
    the Helfgott–Platt Goldbach ladder, previously recorded as **not
    expressible** and 75.1 % of the reference producer's cost.  The
    emitted artifact is 33 KB of C, 3 744 bytes linked, branchless, and
    costs **2.25× GMP's `mpz_powm`** (1.57× with gcc) on the same 91-bit
    modulus.  `prothProgram_denote` proves the artifact's denotation is `0`
    exactly when `a^((N−1)/2) mod N = N − 1`.  Registered as the `proth`
    native certificate.  See `bench/results/tg_proth.md`.
- **Freestanding artifact emission**: emitted artifacts no longer link
  glibc.  A CompCert object for an emitted artifact has zero undefined
  symbols; the dependency was entirely gcc's startup glue.  `ccomp -c` +
  a checked-in `_start` (`runtime/start/`) + `ld` gives a static binary
  with zero undefined dynamic symbols, 70 504 → 1 472 bytes for
  `rolled-10m`.  `check-native` links this way by default (`--hosted`
  restores the old path), and its exit-code classification now
  distinguishes a value disagreement (exit 1, the only such status) from
  abnormal termination (128 + signal), which is never reported as a
  disagreement.  The spurious `#include <lean/lean.h>` is gone.

- **Verification-gate hardening** (audit follow-up):
  - `check-runtime` now fails with status `runtime-missing` when no
    runtime C sources are found, instead of reporting `compatible`
    having checked nothing; `runtime_hash` raises when the project's
    runtime ABI inputs are absent instead of hashing `<missing>`
    placeholders (both were reachable from a non-editable pip install,
    which does not ship `runtime/`).
  - `lean-compcert-probe` exits 3 (not 0) on `probe-incomplete`, so a
    missing `ccomp` can no longer look like success to a caller gating
    on the exit code.
  - The acceptance suite's axiom gate is now an allowlist: any axiom
    outside `propext`/`Classical.choice`/`Quot.sound` — including
    `sorryAx` and bespoke axioms, not just the native-evaluation axioms
    — fails the build. `Computation.result_preserved` joined the audit
    list.
- **Correspondence checkers compare calls in full**: both
  `clight-correspond.py` and the Coq-kernel checker
  (`clight-correspond-coq.py`, `ECall` now carries the destination and
  argument descriptors) compare a call's result destination and every
  argument, not just the callee name; the Coq self-test's mini
  certificate exercises a call, and its negative control must fail at
  the lemma stage (an infrastructure failure no longer counts as a
  rejected mutant). Leading-underscore identifier conflation
  (`lstrip` → `removeprefix`) fixed; function-pointer callees are
  parse errors.
- **`clight-direct-verify.py`** caches `.vo` files keyed on content plus
  the exact `coqc` and CompCert flags (switching toolchains no longer
  reuses a stale cache), and honors `COMPCERT_DIR`/`COQC`; the
  acceptance suite's Coq gates honor `COMPCERT_DIR` instead of a
  hardcoded path.
- **Normalizer**: removing an empty flexible-array member that is not
  the last initializer field no longer leaves a stray comma.
- **Python packaging**: version aligned to 0.2.0 (build manifests
  previously recorded a stale 0.1.0 `backendVersion`).
- Minor robustness: `_CoqProject` token-scan off-by-one, empty
  `-version` output guards, `run_command` no longer treats an explicit
  empty environment as "inherit"; ROADMAP's stale "Sequencing and
  effort" section rewritten to match the implemented milestones.

- **Documentation restructured around the two use cases** — a verified
  `native_decide` (`docs/use-case-1-verified-native-decide.md`) and a
  trusted compiled artifact (`docs/use-case-2-verified-artifact.md`) —
  each stating exactly what is proved and why the method is
  trustworthy; README leads with them, tutorials remain as deep dives.
- **Consumer `check-native`**: `NativeCheck` is exported from the root
  `LeanCompCert` module, gained a repeatable `--include DIR` flag, and
  the `examples/consumer` project wires the cached native cross-check in
  five lines (`consumer check-native`).
- **`check-native`** (`lean-compcert check-native`): cached native
  cross-check pipeline. Emits every registered certificate's generated
  C, compiles it with CompCert, runs the self-checking binary, and
  caches by content hash of the generated C plus ccomp version — only
  certificates whose C actually changed are recompiled and re-run
  (`--force`, `--dir DIR`). The acceptance suite runs it twice and fails
  if the second run is not fully cached. The run remains a cross-check:
  its exit status is never admitted as a theorem.
- **Startup fix**: rolled emission (`Verified/Rolled.lean`) lowered
  against the fully unrolled `toFn` context — at 10⁷ iterations this
  materialized ~10⁸ instructions during module initialization, costing
  ~235 s on *every* CLI invocation. Lowering now uses a `loopCount := 1`
  typing context (`loweringContext`), which declares the identical
  locals; emitted C is byte-identical and startup drops to ~0.4 s.
- `lakefile.toml` version corrected to 0.2.0.
- **Stamp hardening**: `check-native` cache keys now cover the include
  configuration and the *contents* of non-toolchain header directories
  (e.g. the CompCert runtime shim), so editing a shim header or bumping
  the Lean toolchain re-runs affected certificates. Verified: failed
  compiles/runs write no stamps and exit 1.
- README consistency: the proof-boundary section now reflects the
  implemented M6 Clight bridge instead of describing it as future work;
  the versioning section says 0.2.x; use-case 1 states explicitly that a
  bug in this package cannot produce a false theorem — it can only fail
  to typecheck.

## 0.2.0 — 2026-07-28

*(2026-07-29: documentation refresh — five tutorials in `docs/`, README
restructured around the completed roadmap, all tutorial code samples
verified against the build.)*

The verified-computation package release (roadmap M1–M4 milestones and
partial M2/M3/M5/M6/M7; see ROADMAP.md for per-milestone status):

- **Scale-free packaging** (`Verified/Package.lean`): `Program.toComputation`
  with fully structural `wellFormed`/`lowered` evidence.
- **Reflection bridge** (`Verified/Reflect.lean`): register DSL with the
  structural denotation theorem `Program.evalCC_compile`.
- **Rolled loops** (`Verified/Rolled.lean`): rolled emission with the
  complete correspondence `rolledTrace_eq_augmented`.
- **Wide arithmetic** (`Verified/Limb.lean`, `Verified/SignedLimb.lean`,
  `Verified/Log2Fixed.lean`): proved add/sub/compare/multiply/divide,
  sign-magnitude integers, bounded log2.
- **Equivalence library** (`Verified/EarlyExit.lean`,
  `Verified/GcdEquiv.lean`, `Verified/SqrtEquiv.lean`,
  `Verified/Sieve.lean`): early-exit ≡ predicated folds, fixed-shape
  gcd/sqrt equal to `Nat.gcd`/`Nat.sqrt`, fixed-shape smallest-factor
  scan equal to the reference recursion.
- **Certificates** (`Testing/*Certificate.lean`): goldbach-shaped folds
  (§14.1 squarefree Mertens, 128-bit accumulation, fixed-point products),
  axiom-free, CompCert-compiled and executed.
- **CI gates**: axiom audit (no native-evaluation axioms) and clightgen
  translation validation of every certificate unit.
- **Tooling**: batch IR compilation (`scripts/compile-ir-tree.py`) —
  the whole ternary-goldbach `Math` package compiles under CompCert with
  zero rejections.

## 0.1.0 — initial public release
