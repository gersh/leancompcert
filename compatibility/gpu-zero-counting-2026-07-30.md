# GPUs, the last two cited axioms, and whether a GPU result can be trusted

**Date:** 2026-07-30
**Scope:** read-only investigation of `/home/gersh/gpu_prover` (+ 15 worktrees), the two
Lean axiom statements in `claude_math`, and external literature.
**Nothing in `claude_math` or `gpu_prover` was modified.**

The two axioms under examination:

| axiom | file | content |
|---|---|---|
| `finite_check_platt_trudgian_rh_zeta_3e12` | `/home/gersh/claude_math/ext/analytic_nt/AnalyticNT/Chebyshev/PlattTrudgianRH.lean:78` | `RiemannHypothesisUpToHeight 3000175332800` — every zeta zero in the open critical strip with `0 < Im ρ ≤ 3.0001753328e12` has `Re ρ = 1/2`. ~1.2363e13 zeros (`N(3000175332800) = 12363153437138`). |
| `platt_theorem_7_1_dirichlet_verification_source` | `/home/gersh/claude_math/MathExtras/NumberTheory/LSeries/PlattDirichletVerification.lean:70` | `PlattTheorem71DirichletVerification` — for every primitive `χ mod q`, `q ≤ 400000`, every nontrivial zero with `\|Im ρ\| ≤ max(1e8/q, 200 + (7.5e7 or 3.75e7)/q)` has `Re ρ = 1/2`. |

My independent estimate of the Dirichlet workload (totient sieve to `q = 400000`,
`N(T,χ) ≈ (T/π)·log(qT/2πe)`, doubled for `|Im ρ|`): **~1.6e14 zero-verifications** using
`φ(q)` as the character count, **~1e14** after correcting to primitive characters
(`gpu_prover` counts 29,547,446,729 primitive nonprincipal characters, `specifications/TERNARY_GOLDBACH_EXTERNAL_ATOMS.json:122`).
That is consistent with the ~6e13 in the task brief to within a factor ~1.5 depending on
one-sided vs two-sided counting. **The Dirichlet job is ~8-13× the zeta job.**

---

# TL;DR

1. **The $30M CPU figure is wrong by roughly three orders of magnitude, and the reason has
   nothing to do with GPUs.** It measures the wrong algorithm. `acb_dirichlet_platt_hardy_z_zeros`
   isolates *one zero at a time*; Platt–Trudgian's actual published program does *whole-window
   multi-evaluation* — one FFT per 1008-height block yielding ~4,168 zeros at once. Measured on
   this same box family, that is **1.29 ms/zero** versus your 659 ms/zero at index 1e12: a
   **~511× algorithmic gap**, rising to ~1335× at the top of the range.
   Honest CPU cost of the zeta axiom: **4.43e6 core-hours measured** (`gpu_prover` benchmark) /
   7.5e6 core-hours published (Platt–Trudgian) = **506–856 core-years**, i.e.
   **~$37k–$63k at Azure CPU spot, ~$200k–$340k on demand.** Not $30M.

2. **The arithmetic is GPU-friendly, and the prior work already proved that empirically.**
   Platt's windowed program has a *completely fixed* geometry (M=768000 Dirichlet terms,
   K=23 Taylor terms, N1=32768, spacing 21/512) — no data-dependent precision in the hot loop.
   Adaptive-precision ball arithmetic appears only in the rare ambiguous-sample fallback.
   `gpu_prover` has a working CUDA implementation sustaining 9–16 windows/s on a GB10 versus
   0.186 blocks/s on one ARM core: **~50–90× one GPU vs one core, measured.**

3. **No GPU library does rigorous ball arithmetic at Platt's 300-bit isolation precision, and
   none is coming — but the expensive stage doesn't need 300 bits.** `gpu_prover` built its own
   rigorous 106-bit disk arithmetic (double-double centre + *outward* radius, `__dadd_ru`
   error accumulation, the omitted `al*bl` cross term charged explicitly, no non-overlap or
   no-cancellation assumption), plus an exact 192-bit fixed-point phase. It passes the
   sign-usefulness gate where plain binary64 catastrophically failed (101,213 of 131,072 samples
   ambiguous). Caveat: an *empirical* pass at two of 2.97e9 windows, with the bound living in
   CUDA, not in Lean.

4. **Best-case GPU number:** the repo's own cost tables use a 14.3× GB10→H100 *memory-bandwidth*
   roofline, but the branch that actually profiled the kernel found it **FP64-issue-bound at 98%
   of the GB10 DP pipe**. For a DP-bound kernel the right roofline is the FP64 ratio,
   **~70×** (H100 34 TFLOP/s vs GB10 0.49). At 70× on 8 confidential H100s: **~1,280 node-hours,
   ~6.7 days, ~$1,816 spot / ~$8,931 on demand** for the FFT+Taylor stages. **Zero H100 runs of
   this workload have ever happened.** Every H100 figure in the repo is a projection.

5. **Half two: no verified-compilation story for GPU exists and none is coming.** No CompCert
   for CUDA/PTX/SASS at any pipeline stage. `ptxas` is a closed binary emitting an ISA with no
   published semantics, and it has confirmed wrong-value bugs on record. H100 CC attestation
   covers **GPU firmware only** — not the cubin, not memory contents, not the result — and was
   demonstrably relay-attacked in 2025 against Phala's exact stack. **Attesting a GPU run buys
   you nothing about the arithmetic.**

6. **The checker/prover asymmetry is the right idea, is already the repo's architecture, and
   is currently the binding constraint rather than the solution.** The Lean-side bracket checker
   is fully proved and axiom-free — and runs at **22 brackets/s**, projecting to ~5e4 core-years
   for a 3.8e13-zero certificate. The asymmetry is real in principle (a sign check needs ~50 bits;
   finding the zero needs 300) but has never been engineered, and the certificate is inherently
   linear in the zero count (~1.24e13 brackets).

**Blunt bottom line:** GPUs do not decide this. The zeta axiom is *already* a $40k–$200k CPU job
if you run Platt's actual algorithm instead of the per-zero isolator, and a GPU port plausibly
takes it to ~$2k–$10k. What blocks discharge is **not cost** — it is that (a) there is no Hardy Z
function in Lean, (b) there is no formal Turing/argument-principle theorem, (c) the certificate
is 1.24e13 brackets that the Lean kernel checks at 22/s, and (d) nothing in the GPU trust chain
survives contact with `ptxas`. **These two axioms stay cited regardless of hardware. The reason
is the formalization gap, not the compute bill.**

---

# HALF ONE — Can GPUs make the last two axioms feasible?

## 1.1 The CPU baseline in the brief measures the wrong algorithm

Your measurements (`acb_dirichlet_platt_hardy_z_zeros`, 8.57 / 23.24 / 64.17 / 193.34 ms at
n = 1e8/1e9/1e10/1e11, 659 ms at 1e12) are of Arb's **single-zero isolator**. Integrating your
own fit `8.57·(n/1e8)^0.4535` ms to n = 1.2363e13 gives an average 1.20 s/zero and
**4.7e5 core-years** — consistent with your 6.8e5.

`gpu_prover` measured the *other* route, on the same DGX Spark ARM CPU:

> "On the local DGX Spark ARM CPU, eight consecutive source-height blocks took `43.03 s`, or
> `5.37875 s/block`, with about `281 MB` peak RSS. Straight scaling gives approximately
> `4.43 million` one-core hours for the high range. This is consistent with the roughly
> `7.5 million` core-hours reported for the original computation and explains why merely
> deploying the CPU executable to Azure is not sufficient."
> — `/home/gersh/gpu_prover/docs/algorithms/PLATT_PT21_WINDOWED_SOURCE_CAMPAIGN.md:148-153`

Geometry (`same file:104-112`): the campaign starts at `10^10` with `N(10^10) = 32130158315`,
runs `2966443783` blocks × 1008 height, ending at `3000175333264` (deliberately 464 above the
theorem endpoint, proving slightly more rather than rounding). Known-answer counts:
3399 zeros in `[1e10, 1e10+1008]`, 4314 in `[3e12, 3e12+1008]` (`:56-60`).

Derived:

| quantity | value |
|---|---|
| blocks | 2,966,443,783 |
| average zeros/block | 4,167.7 |
| **CPU cost per zero (windowed route)** | **1.29 ms** |
| CPU cost per zero (Arb isolator @ index 1e12, your measurement) | 659 ms |
| **algorithmic ratio at index 1e12** | **511×** |
| algorithmic ratio at index 1.24e13 (your fit → 1.749 s/zero) | 1355× |
| total | 4.432e6 core-hours = **506 core-years** |
| Platt–Trudgian published | 7.5e6 core-hours = 856 core-years |

Cost at the prices `gpu_prover` captured for East US 2 on 2026-07-21
(`docs/AZURE_PERFORMANCE_SIZING.md:118-126`: `Standard_DC96as_v6` = $4.358/node-hour PAYG,
$0.805358 spot, 96 cores):

| route | core-hours | spot | on demand |
|---|---:|---:|---:|
| windowed (repo-measured) | 4.43e6 | **$37,182** | $201,201 |
| Platt–Trudgian published | 7.5e6 | **$62,919** | $340,469 |
| Arb per-zero isolator (your baseline) | 4.1e9 | $34.7M | $187M |

Note that the repo's own *headline* zeta cost — "11.16 years / $1.706M PAYG / $315,272 spot"
(`AZURE_PERFORMANCE_SIZING.md:294-302`) — is also for the wrong route: it is the FLINT
`count-only` local isolator projected at 37.58M process-hours. The repo says so:
`specifications/TERNARY_GOLDBACH_EXTERNAL_ATOM_READINESS.json:606` — *"Platt zeta RH at 3e12 and
the historical full-range Goldbach campaign are implemented only through economically
impractical reference/source routes."*

**So the first honest finding is that this is not a GPU question at all.** Running Platt's own
published program on rented CPU is a ~$40k–$200k job today.

## 1.2 What is the arithmetic actually doing?

Platt's windowed program is an Odlyzko–Schönhage-style band-limited multi-evaluation of the
Hardy Z function via Gaussian-windowed sinc interpolation, executed with a **fixed, height-independent
geometry** (`PLATT_PT21_WINDOWED_SOURCE_CAMPAIGN.md:64-68`):

> "The source fixes sample spacing `21/512`, FFT length `131072`, intermediate FFT length
> `32768`, `768000` Dirichlet terms, and `23` Taylor terms. A step of `1008` is exactly `24576`
> samples."

Exact work counts per block (`:157-172`):

```
23 × 4 × (32768/2) × 15 + (65536/2) × 16 = 23,134,208 radix-2 butterflies
23 × 768,000                             = 17,664,000 Dirichlet/Taylor term visits
```

Full high range: **6.8626e16 interval FFT butterflies + 5.2399e16 term visits.**

**This answers the bottleneck question directly.** The hot loop is a fixed-length FFT plus a
fixed-length Taylor/Dirichlet sum. There is **no data-dependent precision in it**. Adaptive
precision appears only in two places, both off the critical path:

- **Ambiguous-sample fallback.** When an output disk straddles zero, the sample is replayed on
  the host in Arb at fixed 2176 bits (`:784`, `PLATT_PT21_FUSED_EVENT_STREAM.md:200`). On the
  qualified DD/Q192 path this rate is **zero**: "zero invalid and zero ambiguous disks among
  `1,647,424` required samples per sample" at *both ends* of the campaign (`:737-743`).
- **Stationary-point resolution and Turing endpoints**, at 128/256 bits
  (`reference/tg_platt_pt21_turing_inputs.cpp:39-40`: `kRetainedPrecision = 128`,
  `kReplayPrecision = 256`).

So: **the bottleneck is FFT/Taylor throughput at fixed precision, which is exactly the
GPU-friendly case.** The GPU-hostile case (Arb's adaptive-precision ball arithmetic with
per-value heap allocation and divergent limb counts) is confined to a fallback that the
qualified path never triggers.

Independent confirmation from the profiling branch (`agent/h100-gpu-path`, commit `c3c17b3`):

> "SASS census of `dd_radix2_stage` shows 531 DP instructions on sm_90 (2,120 of 2,744 slots are
> literal NOP on sm_121), and an ILP microbenchmark saturates the GB10 DP pipe at 205.7 Gdadd/s
> with ILP=1, where the baseline kernel already sits at 98%."

The kernel is **FP64-issue-bound**, not bandwidth-bound. That is a pure-arithmetic profile.

## 1.3 Is there a GPU library doing rigorous high-precision interval/ball arithmetic?

**No. Flatly no, and this is the honest answer.**

- **No GPU port of Arb, FLINT, MPFR, MPFI, or any ball-arithmetic library exists.** Fredrik
  Johansson (Arb/FLINT author), Sage Days 2022 slides p. 17, verbatim: *"Arbitrary-precision types
  are not suited for vector processing (SIMD, GPU) — Convert to vector-friendly representations."*
  "Double and double-double ball arithmetic" is listed as an *idea*, still unimplemented in
  FLINT 3.x. https://www.fredrikj.net/math/sagedays2022flint.pdf
- **No GPU interval library above binary64.** CUDA does have per-instruction directed rounding
  (`__dadd_ru/_rd`, `__dmul_ru/_rd`, `__fma_ru/_rd`, …) which is *better* than the CPU's global
  mode register. But NVIDIA's `cuda_interval_lib.h` sample specializes only `float` and `double`,
  and NVIDIA confirmed on their forums (Jan 2025) they ship no official interval library. The
  research lineage (Collange–Flórez–Defour RNC8 2008; GPU Computing Gems ch. 9, 2011;
  arXiv:2507.20769, Jul 2025) is entirely double-precision.
- **Nobody has combined directed rounding with multi-double expansions.** That object —
  outward-rounded extended-precision GPU intervals — does not exist in the literature or on GitHub.
- **Extended-precision GPU libraries are dead or unsuited.** CAMPARY (last release ~2016, proves
  round-to-nearest relative-error bounds, no directed rounding, no transcendentals);
  GQD/GARPREC (dead 2010; authors state outright *"algorithms for most mathematical functions with
  extended precision do not have theoretical error bounds"*, DaMoN 2010 §4.1); CUMP (archived
  2012); XMP/CGBN (alive, but **unsigned integers only** — a ZK/crypto bignum library, no floats);
  MPRES-BLAS (2022, RNS, no rounding control). Arpra is CPU/MPFR, not GPU.
- **No published GPU zeta implementation at all**, rigorous or not — no GPU Odlyzko–Schönhage,
  no GPU Riemann–Siegel, no GPU Turing's method. Every large zeta computation
  (Gourdon–Demichel 2004; Bober–Hiary arXiv:1607.00709; Platt Math. Comp. 86 (2017);
  Platt–Trudgian arXiv:2004.09765 on NCI Raijin/Gadi) is CPU.

**Is double-double enough for ±2⁻¹⁰²? No, not for the isolation step.**
±2⁻¹⁰² is an *absolute* precision on the ordinate. At height 3e12 ≈ 2^41.4, naming the answer needs
~143 bits of *relative* precision before any arithmetic. Platt used **300 bits of MPFI** to reach
that target (Math. Comp. 86 (2017), 2449–2467). DD gives ~106 bits nominal, and less in practice:
Joldes–Muller–Popescu (ACM TOMS 43(2), 2017) prove DD relative errors of 3u²–9.8u² with u = 2⁻⁵³,
i.e. **you lose 1.5–3.3 bits per operation off the nominal 106**, compounding. Worse,
Muller–Rideau (ACM TOMS, 2022, doi 10.1145/3484514) found **errors in some of those original
proofs** while formalizing them in Coq. Quad-double's renormalization is openly unproven by its
own authors (Hida–Li–Bailey), and MultiFloats.jl removed Float64x5–x8 for algorithmic defects.

Cost of the precision levels that *would* clear 300 bits (Verschelde, arXiv:2110.08375, Table 1):

| format | add | mul | div | avg overhead vs FP64 |
|---|---:|---:|---:|---:|
| double-double (106 b) | 20 | 23 | 70 | **37.7×** |
| quad-double (212 b) | 89 | 336 | 893 | **439×** |
| octo-double (424 b) | 269 | 1742 | 5126 | **2379×** |

Octo-double on an H100: 34 TFLOP/s ÷ 2379 ≈ **14 GFLOP/s** — a single CPU core running Arb at
300 bits is competitive. FP64 tensor cores (67 TFLOP/s) are unusable here: error-free transforms
need the exact rounding residual of each scalar op, which tensor cores do not expose.

### What `gpu_prover` built instead, and why it is the interesting counterexample

**Important qualification to the "no rigorous GPU high-precision arithmetic" answer above:** no
*library* exists, but this repo built a purpose-specific one, and it is genuinely rigorous ball
arithmetic — not heuristic, despite the "sloppy" naming.

The carrier type (`gpu/include/sparkinterval/tg_platt_windowed.hpp:33-52`) is
`RealDisk106{center: DoubleDouble, radius}` / `ComplexDisk106{real, imaginary, radius}`:
*"A complex Euclidean disk whose Cartesian center is the exact mathematical sum of two binary64
limbs. `radius` encloses every uncertainty not retained in those limbs."*
So: ~106-bit centre, and **every residual is charged outward to the radius rather than dropped.**
"Sloppy" refers only to skipping the `al*bl` cross term and low-limb renormalization, and that
omission is explicitly paid for
(`docs/algorithms/PLATT_PT21_DD_SLOPPY_MUL_QUALIFICATION.md:24-56`): with
`kappa = 0x1.0000000000001p-53` (an upward binary64 bound for `u/(1−u)`), `eta = 2^-1074`, and
`E(r) = RU(kappa·|r| + eta)`, the outward centre error is
`eta + E(c0)+E(c1)+E(c)+E(low) + RU(|al|·|bl|) + 6·eta`, with the explicit claim:
*"The omitted `al*bl` product is charged explicitly. **No non-overlap, normalization, relative
limb-size, normal-result, or no-cancellation assumption is made.**"* The kernels use `__dadd_ru`
/`__dmul_ru` exclusively for error accumulation and `finite_status()` fail-closed on every
intermediate (`reference/tg_platt_dd_sloppy_mul_qualification.cu:140-142, 243-286`). Builds require
`--fmad=false --ftz=false`.

**Qualification outcomes (all PASS, all differential/containment, none a correctness proof):**

| artifact | criterion | outcome |
|---|---|---|
| `tg_platt_dd_sloppy_mul_qualification.cu` | independent exact `cpp_rational` dyadic check of the `MulCertificate` obligations, 8,192-row corpus | **PASS** |
| `tg_platt_dd_sloppy_root_whole_transform_qualification.cu` | exact disk **containment** of candidate over ordinary, all 131,072 disks, *"no floating-point tolerance, sampled subset, overlap substitute, or centre-only fallback"* | **PASS** |
| `tg_platt_dd_tile9_qualification.cu` | **byte-for-byte** equality of all 131,072 `RealDisk106` outputs | **PASS**, not selected |
| bitreverse+tile9 | byte identity + containment + resource gate | **PASS**, not selected |
| `*_api_smoke.cu` | finiteness, fail-closed forgery roster, inactive-cell exact zero | **PASS** |

Every runner forcibly reports `performance_evidence_eligible=false` (cannot detect
profiler/sanitizer injection), `optimization_selected_for_production=false`,
`physical_refinement_proved=false`, `pt21_source_claim_discharged=false`. One partial failure is
kept honest and non-gating: *"the initial run found that 130,065 cells do not satisfy
candidate-contains-ordinary: their radii round to the same binary64 value while their retained
centres differ. That fact remains explicit and non-gating; it was not rewritten as containment"*
(`PLATT_PT21_DD_SLOPPY_ROOT_WHOLE_TRANSFORM_QUALIFICATION.md:191-195`; synthetic finite-edge case).

**Achieved widths** (`PLATT_PT21_WINDOWED_SOURCE_CAMPAIGN.md:516-518, 675-677, 736-740`):
transformed radii 3.678e-13 (first block) to 1.853e-10 (terminal); Gamma producer radii 4.436e-25
to 2.221e-22 versus ~4.97e-17 for the failed binary64 V1; accumulator required radius 2.1045e-32
versus 1.0868e-31 produced. Comfortable margin — but *measured at two of 2,966,443,783 windows*.

**The architecture.** It does not attempt 300-bit GPU arithmetic. It splits the dynamic range:

- The huge-exponent part (the phase `t·log n` at height 3e12) is carried as an **exact 192-bit
  fixed-point integer reduced mod 2^192** — integer arithmetic, no rounding at all
  (`PLATT_PT21_WINDOWED_SOURCE_CAMPAIGN.md:238-247`).
- The local trig is evaluated as **double-double sine/cosine Taylor disks** on an octant-reduced
  argument, degree 17/18 (`:238-241`, `:671`).
- The FFT butterflies are **directed-rounded binary64 intervals** (`:207-212`).
- Everything is audited against directed 256/320-bit MPFR checkers (`:241`, `:514`, `:673`).

This is precisely the "one conservative fixed precision, branch-free, CPU fallback for the rare
hard cases" architecture that is the only viable GPU design. **And there is a hard empirical
qualification result confirming that plain binary64 is not enough and the DD/Q192 path is:**

- V1 binary64-only disk transform: *"**101,213 of 131,072 real samples were ambiguous**. The
  implementation therefore fails the sign-usefulness gate on the actual first window even though
  every output disk is finite."* (`docs/algorithms/PLATT_WINDOWED_DISK_SEMANTIC_PROTOTYPE.md:212-219`)
- Binary64-only accumulator centre: *"measured and rejected because its roughly `10^-16` bucket
  radii were unsuitable for the downstream sign test."* (`:507-509`)
- V1 fused worker: 41 sign-ambiguous disks *"because the binary64 coefficient boxes had already
  lost too much width."* (`:724-728`)
- Qualified DD/Q192 path: *"zero invalid and zero ambiguous disks among `1,647,424` required
  samples"* at both campaign endpoints (`:737-743`).

**Caveats, stated plainly.** (i) That is a *sampled empirical pass at two of 2.97 billion blocks*,
not a proven error bound over the range — the repo says so: *"It does not prove useful widths at
every one of 2,966,443,783 windows"* (`:742-743`). (ii) The composed error bound lives in CUDA and
Python, not in Lean or Coq. (iii) There is a hard precision failure on record for the obvious
optimization: reusing a transform across neighbouring windows gave ~15,270 ambiguous disks at
`delta = ±1` and **all 25,741 ambiguous** at `delta = ±2` at interior block 2, now retained as a
negative regression test (`:842-848`).

So the corrected form of the answer to "is there a GPU library doing rigorous ball arithmetic at
Platt's precision" is: **no library, and 300 bits on a GPU is hopeless (14 GFLOP/s of octo-double
on an H100) — but the full 300 bits are needed only for final isolation to ±2⁻¹⁰², and the
multi-evaluation stage that dominates the cost demonstrably runs in rigorous 106-bit disk
arithmetic.** That is a real and non-obvious result, and it is this repo's, not the literature's.

## 1.4 Best-case GPU speedup and cost

**Measured, one device vs one core:** GB10 fused transform+event rate 9.2043 windows/s
(`PLATT_PT21_WINDOWED_SOURCE_CAMPAIGN.md:737-743`) vs 1/5.37875 = 0.1859 blocks/s per ARM core
→ **49.5× per GB10 vs one core.** The optimized gpu-path branch reached 16.46 windows/s
(commit `c3c17b3`) → **88.5×**. The repo never states this ratio; it always frames things as
*required uplift*, so I derived it.

**GB10 → H100.** This is where I disagree with the repo's own tables. Every cost row in
`AZURE_PERFORMANCE_SIZING.md` and `PLATT_PT21_WINDOWED_SOURCE_CAMPAIGN.md` uses a **14.3×**
multiplier, explicitly disowned as *"only the `3.9 TB/s / 273 GB/s` H100-NVL-to-DGX-Spark
**bandwidth** roofline"* (`AZURE_PERFORMANCE_SIZING.md:225-231`). But the branch that profiled the
kernel found it FP64-**issue**-bound at 98% of the DP pipe. For a DP-issue-bound kernel the correct
roofline is the FP64 throughput ratio:

- H100 SXM/PCIe FP64 vector: **34 TFLOP/s** (H100 NVL: ~30). Peak non-FMA dadd:
  8448 FP64 lanes × 1.755 GHz ≈ **14.8 Tdadd/s**.
- GB10 measured: **205.7 Gdadd/s** (repo microbenchmark), **0.49 TFLOP/s** FP64 (your measurement;
  GB10 is 1:64 FP64:FP32 per chipsandcheese, 2026-03-14).
- **Ratio ≈ 70×** (69× on TFLOP/s, 72× on dadd/s).

That is comfortably above the 28.6×–29.2× the repo says it needs
(`PLATT_PT21_WINDOWED_SOURCE_CAMPAIGN.md:463-470, 800-805`). **The repo's cost tables are
pessimistic because they used the wrong roofline.** This was independently confirmed from the
kernel side: the ordinary root-multiplication kernel executes **374 scalar FP64 arithmetic
instructions** (164 for the sloppy candidate), at 61–80 registers with no local spills
(`PLATT_PT21_DD_SLOPPY_MUL_QUALIFICATION.md:137-143`) — an unambiguously FP64-ALU-bound profile,
justified in the cost tables by a *memory-bandwidth* ratio. The repo characterizes GB10's FP64 rate
nowhere in `docs/`.

**The corroborating evidence that this is an arithmetic wall, not a plumbing wall, is that every
non-arithmetic optimization tried has failed to move it:** tile9 1.00355× (ranges overlap, i.e.
noise), joint tile9+sloppy 0.226% over settled, bitreverse+tile9 2.21%, two-slot recentered
pipeline 2.87% — and the pipeline doc concludes *"these kernels contend for device resources…
Four slots cannot remove the single serial transform bottleneck. It is therefore not implemented"*
(`PLATT_PT21_RECENTERED_PIPELINE.md:164-167`). The only large win was arithmetic:
the bounded-sloppy DD multiply, 2.2176× isolated / 1.175× whole-transform, from cutting 374 FP64
instructions to 164. **The DD butterfly FP64 arithmetic *is* the wall — which is exactly why the
FP64-ratio roofline, not the bandwidth roofline, is the one that governs the H100 uplift.**

**Resulting numbers, best case, at 70× on 8 confidential H100s:**

| | value |
|---|---:|
| effective rate/device | 644 windows/s |
| total device-hours | 1,280 |
| wall time on 8 devices | **6.66 days** |
| cost @ $1.419034/node-hour spot | **$1,816** |
| cost @ $6.98/node-hour on demand | **$8,931** |

**Pricing check: $1.419/GPU-hour still holds.** Queried live from the Azure Retail Prices API
on 2026-07-30: `Standard_NCC40ads_H100_v5` (1× H100 NVL 94 GB, SEV-SNP + NVIDIA CC, 40 Genoa
cores) — East US 2 **$6.98 on demand / $1.419034 spot**; Central US $7.89/$1.46; West Europe
$8.90/$1.64. Spot meters are monthly and expire 2026-07-31. Notably the *confidential* SKU is
**72% cheaper on spot** than the non-CC NC40ads ($1.419 vs $5.026) — nobody bids on confidential
GPU inventory. Market context: RunPod H100 SXM $2.99/$2.69, Verda $3.25/$1.14 spot (market floor),
Lambda $4.29, Phala H100 TEE $3.08 on demand. AWS has no confidential H100 at any price
(NVIDIA/nvtrust#65).

**Everything above is a projection.** Blunt statement of the evidence base:

> **No H100 has ever executed any of this workload.** `docs/GPU_MODEL.md:14` classifies H100 as
> *"Diagnostic and primitive device artifacts built offline; **no H100 execution**"*. The gate
> `h100_calibration_passed` has never been cleared and `target_h100_measured = false` in every
> qualification doc. The only trace of a real H100 anywhere is an API-smoke digest match in
> commit `c3c17b3` — a correctness/identity check with no throughput recorded.

And the 6.66-day figure covers **FFT + Taylor arithmetic only**. Excluded, per the repo's own
disclaimer (`PLATT_PT21_WINDOWED_SOURCE_CAMPAIGN.md:180-185`): input generation, ambiguous-block
CPU replay, interpolation, zero isolation, Turing checks, the prefix below 1e10, storage, retries,
and attestation. The repo's honest current 2-stage composition needs 16 nodes for
**$18,762 PAYG / $3,814 spot at exactly 7 days** (`:451-470`), and it says: *"this 16-node shape
can fit both the time and `$10k` constraints only with discounted/Spot capacity."*

**Net GPU verdict for zeta: GPUs take a ~$40k–$200k CPU job to a ~$2k–$19k GPU job.**
That is a real 10–20× cost win, but it is a win on a number that was already affordable. It is
not the difference between impossible and possible.

## 1.5 The Dirichlet axiom

Much worse, and the repo is explicit:

- **No ETA exists.** `docs/algorithms/GRH_POC_BENCHMARKS.md:117`: *"There is no defensible full-run
  H100 ETA yet."* `AZURE_PERFORMANCE_SIZING.md:564-565`: *"V3 therefore remains component evidence
  rather than a Theorem 7.1 ETA."*
- Work shape: 29,547,446,729 primitive nonprincipal characters for q=2..400000,
  1.5335e16 butterflies, 2.667e14 residue reconstructions
  (`specifications/TERNARY_GOLDBACH_EXTERNAL_ATOMS.json:122`).
- Best available *component* budget (not the campaign): 6,004–6,021 CPU-hours + 138.6–211.5
  GPU-hours, **$112,399–$116,775 on demand / $20,914–$21,799 spot**
  (`AZURE_PERFORMANCE_SIZING.md:618-625`).
- Historical scale: Platt reported ~400,000 core-hours; ideal division over four 96-core nodes is
  1,041.7 h (43.4 days), ~$18,158 PAYG / $3,356 spot — *"Those values are not an estimate for the
  current code"* (`:660-663`).
- **A live correctness problem, not just a cost problem.** The `agent/dirichlet-turing-bound`
  worktree **numerically refutes the `+2h` term in Platt's printed Theorem 3.2** over six
  conductor/window rows, and separately finds a bug in the released `im_int2`:
  *"The odd branch `im_int2` (`s = 3/4`) should use `-3/32` but uses `-15/32`, and it computes
  `atan(t/3)` where `atan(4t/3)` is intended"*, worth −1.31 inside the bracket at t₀=60, h=100,
  *"which exceeds the routine's own declared error ball"*
  (`docs/algorithms/DIRICHLET_TURING_REFLECTED_BOUND.md:279-292, 322-326`).
  Also: the constants Platt attributes to Trudgian (personal communication, unpublished) must be
  replaced by Rumely's 1993 published ones, which have not yet been checked against the paper
  (`:393-395`).

Since Platt's ~400,000 core-hours is *smaller* than the zeta job's 7.5e6, the Dirichlet axiom's
obstacle was never compute either — it is that the literature has defects that must be repaired
before a computation could even be specified correctly.

---

# HALF TWO — How can a GPU computation be trusted?

## 2.1 What an H100 CC attestation actually covers

I had the NVIDIA verifier source and reference manifests read rather than the marketing pages.
The attestation report is an SPDM `GET_MEASUREMENTS` response signed by a per-chip Attestation Key,
and it contains exactly two things:

**(a) 64 measurement records** `{index, spec, size, SHA-384}`. From NVIDIA's own GH100 reference
manifests (`.swidtag`, ISO 19770-2 SWID): the VBIOS RIM covers indices 0–63 (entries 1–6 named
`HashedMeasurement_N_FSP` — the on-die RISC-V Falcon Security Processor); the Driver RIM covers
indices 32–38 named `HashedMeasurement_N_GSP` — **the GSP firmware images shipped with a driver
version, not the host kernel module binary**. All entries are firmware/config hashes.

**(b) An OpaqueData blob** with a fixed field list: `CERT_ISSUER_NAME`, `DRIVER_VERSION`,
`GPU_INFO`, `SKU`, `VBIOS_VERSION`, `MANUFACTURER_ID`, `TAMPER_DETECTION`, `VPR`, `BOARD_ID`,
`CHIP_SKU`, `FWID`, `PROTECTED_PCIE_STATUS`, `LOCK_SWITCH_STATUS`, `FEATURE_FLAG`, … (from
`spdm_msrt_resp_msg.py`). Resulting EAT/JWT claims are `measres: "success"`, `secboot: true`,
`dbgstat: "disabled"`, `hwmodel: "GH100 A01 GSP BROM"`, driver/VBIOS version strings, nonce, UEID.

Direct answers:

| does the H100 attestation cover… | |
|---|---|
| (a) GPU firmware / VBIOS measurement | **YES** — this is essentially its entire content |
| (b) driver | **version string only**, plus hashes of the *GSP firmware* in that driver bundle |
| (c) the CUDA kernel binary / cubin you loaded | **NO** — zero claims, zero measurement slots |
| (d) contents of GPU memory | **NO** |
| (e) the computed result | **NO** |

The IBM Research / Ohio State reverse-engineering study states it flatly: the report validates
*"device identity, VBIOS and firmware measurements, and current security settings"*, establishing
GPU trustworthiness **at initialization time, not workload execution**
(arXiv:2507.02770 §8, https://arxiv.org/html/2507.02770v1).

**Two architectural facts people get wrong.** From NVIDIA's own HCC whitepaper (WP-11459-001,
p. 28): *"The compute engines execute **unencrypted code on unencrypted data** resident in GPU
memory"* and *"The on-package HBM memory … **is not encrypted**."* H100 CC is **access control**
(a hardware firewall around ~90% of HBM designated the Compute Protected Region, plus AES-256-GCM
on the PCIe bounce-buffer path), **not memory encryption**. Any vendor page claiming "encrypted
VRAM" is wrong.

**Nobody measures your kernel, by design.** The only application-code measurement anywhere is
CPU-side: e.g. dstack extends RTMR3 with a `compose-hash` of `app_compose.json` (Docker image
digest + args + env). That transitively covers your app only if the image digest pins everything
and the build is reproducible — and it says nothing about which cubin the CUDA runtime JITs.
NVIDIA is explicit that this is intentional: *"running Compute applications is identical to a
regular GPU … executing your kernels should be transparent."*

The attackers put it best (TEE.fail §8.3):

> "…it provides a hardware attestation that proves the CPU interfaces directly with a genuine
> CC GPU. However, **the attestation does not identify what the GPU is running.**"

**Does attestation say anything about numerical correctness? No, on every axis.**
RFC 9334 (RATS Architecture) defines Evidence as *"configuration data, measurements, telemetry,
or inferences"* and attestation as establishing that a peer *"is in an intended operating state"* —
there is no correctness-of-output claim in the architecture, and the spec warns state may change
immediately after Evidence generation. Structurally there is nothing in the H100 report that
*could* express it: 64 firmware hashes and a fixed field list, no input digest, no output digest,
no kernel digest. NVIDIA's three stated CC goals (whitepaper p. 13) are confidentiality, integrity
against host alteration, and basic physical attack resistance. And NVIDIA explicitly disclaims even
*determinism*: *"the final values computed using IEEE 754 arithmetic can depend on implementation
choices such as whether to use fused multiply-add or whether additions are organized in series or
parallel"* (CUDA Floating Point and IEEE 754 Compliance guide). **A malicious-but-signed kernel, a
buggy kernel, and a correct kernel produce identical attestations.**

`gpu_prover`'s own documentation reaches the same conclusion independently and states it well
(`docs/AZURE_CONFIDENTIAL_COMPUTE.md:26-31`):

> "The final arrow is a declared trust boundary. Attestation supplies evidence about measured
> platform state and nonce freshness; it does not make a false program correct, prove that
> arbitrary user-space code produced an output, or replace review of the closed algorithm and
> its execution harness."

and (`:60-66`):

> "A valid quote proves that the certified vTPM signed the stated qualifying data and PCR state.
> It does not, by itself, prove that the named program caused the output: sufficiently privileged
> guest code could request a quote or extend an unrestricted PCR."

### The relay attack: this was broken in practice, against Phala specifically

**TEE.fail** (Chuang, Seto, Berrios, van Schaik, Garman, Genkin — Georgia Tech / Purdue,
IEEE S&P 2026; https://tee.fail/, paper at https://tee.fail/files/paper.pdf). A <$1,000 DDR5 bus
interposer defeats Intel TDX/SGX and AMD SEV-SNP (deterministic AES-XTS, no Merkle-tree integrity
on server TEEs); they extracted the Intel PCE attestation key and forged DCAP quotes.
**The GPU consequence is the one that matters here:**

> "As NVIDIA does not bind the H100 to identities of specific VMs, our malicious VLLM-PROXY
> successfully passes both TDX and CC attestations."

They demonstrated a **GPU relay attack**: an RTX 3060 in a non-TDX box forwarding GPU attestation
calls to a rented H100 elsewhere. Victims verified against NVIDIA and were cryptographically
convinced their work ran on a CC H100. They observe *"a provider could multiplex a single H100 to
provide attestations for hundreds of instances."* **This was demonstrated against dstack — Phala's
stack — and Phala/NEAR AI's `vllm-proxy`.** Disclosed to NVIDIA June 2025.

Other published findings: RPC metadata leakage (physical address tables and queue headers plaintext
in staging buffers, findable by a 4 KB-stride scan), bimodal transfer-latency timing channels,
SEC2 can decrypt/verify but not encrypt (semaphores and pushbuffers observable by the host)
— arXiv:2507.02770, disclosed to NVIDIA PSIRT.

*Two things frequently miscited as H100 CC breaks and are not:* **GPUHammer** (USENIX Sec 2025) is
GDDR6 on RTX A6000/3060 — H100 uses HBM3 with always-on on-die ECC and no demonstrated flips;
**MOLE** (CCS 2025) is Arm Mali and only speculates about extension to NVIDIA.

### CC-mode operational costs

Disabled or limited in CC-On: performance counters (side-channel vector; `CC-DevTools` re-enables
them and correspondingly weakens security), JTAG, `cudaHostRegister()`, MIG, vGPU. Multi-GPU CC is
**not supported on Hopper** — the multi-GPU path is Protected PCIe, mutually exclusive with CC per
GPU, and **NVLink traffic remains unencrypted on Hopper**. Host↔device DMA is capped around
**4 GB/s** by CPU-side encryption. Measured overheads: 6.85%–19% for large-batch LLM inference
(arXiv:2409.03992), +21.8%/+27.8% TTFT and −17.7%/−21.1% throughput on TDX (arXiv:2607.19353),
and **8× average, up to 41.6× worse** for 4-GPU DDP training (arXiv:2501.11771) because
ring-all-reduce must encrypt and MAC every hop through the CPU.

**For this workload the 4 GB/s DMA cap and single-GPU-per-VM restriction are the binding
constraints**, not the arithmetic overhead — and 8 separate single-GPU confidential VMs is exactly
the shape the repo's cost tables already assume.

## 2.2 Which links of the CPU chain survive on GPU?

Our CPU pattern: **Lean proves `Program → C`; CompCert proves `C → machine code`; the enclave
attests the run; Lean proves `bytes → claim`.**

| link | GPU status |
|---|---|
| Lean proves `Program → C` | **Survives, in a narrow form.** `gpu_prover` has a real, fully proved compiler from a typed interval-polynomial AST to a modelled PTX machine. See §2.3. |
| CompCert proves `C → machine code` | **Does not survive. Nothing replaces it.** |
| enclave attests the run | **Survives only as provenance**, and was relay-attacked (§2.1). It never covered the kernel or the result. |
| Lean proves `bytes → claim` | **Survives** — this is the certificate-checking half, and it is the one genuinely healthy link (§2.4). |

**There is no verified-compilation story for GPU kernels at any pipeline stage.** The honest
state of the art:

- **The one strong result** — Lustig, Sahasrabuddhe, Giroux, *A Formal Analysis of the NVIDIA PTX
  Memory Consistency Model*, ASPLOS 2019 (doi 10.1145/3297858.3304043). Axiomatic model of PTX
  ISA 6.0, Alloy encoding, and — via a new Alloy→Coq compiler `alloqc` — a **machine-checked Coq
  proof (~3100 lines) that the scoped-C++→PTX mapping is sound for programs of any size**.
  **Scope: memory consistency model only.** Not functional correctness. Alloy checks bounded to
  4–6 events. The proof is about the *spec document*, not the silicon. PTX 6.0 is Volta-era —
  **Hopper's `wgmma`, TMA `cp.async.bulk.tensor`, `mbarrier`, and distributed shared memory have
  no public formal model at all.**
- **GPUVerify** (OOPSLA 2012 / TOPLAS 2015): race and barrier-divergence freedom only, via a
  two-thread abstraction to Boogie/Z3. No functional correctness, **assumes sequential
  consistency** (hence unsound w.r.t. the real PTX weak model), **unmaintained since 2022-07-28**.
  Live successors: Faial (Coq-mechanized DRF, but 98% of programs need a fixed thread config),
  GPUMC (CAV 2025, arXiv:2505.20207 — first checker respecting the weak model).
- **PTX operational semantics**: Habermaier TR 2011-14; Habermaier & Knapp, ESOP 2012 (proves SIMT
  execution agrees with per-thread scalar semantics — the closest thing to a semantics-preservation
  theorem in GPU-land, *on paper, unmechanized*); CUDA au Coq, DATE 2019 (Coq operational PTX
  semantics, explicitly designed to *avoid* needing a verified compiler); ROCetta (executable PTX
  semantics + SMT-LIB beta Feb 2026; SASS side only Pascal / partial Volta).
- **`ptxas` is the hard wall.** A closed-source binary emitting SASS, an ISA for which NVIDIA
  publishes **no semantics at all**. The black-box evidence is not clean: CUDAsmith (COMPSAC 2020)
  found a **confirmed wrong-value bug in nvcc 9.0/9.1** and **a confirmed `ptxas` bug in nvcc 8.0**.
  Lifters cover a fraction (NVLift, BAR@NDSS 2026: 47 SASS instructions on Turing).
- **The spec↔silicon gap is not hypothetical.** GPUHarbor (ISSTA 2023) tested 106 devices from 7
  vendors and found **conformance bugs on shipping NVIDIA hardware**, including a coherence (RR)
  violation on a Quadro P620.
- **Floating point.** NVIDIA guarantees correct rounding for fp32/fp64 add, mul, FMA, div, sqrt;
  **not** for transcendentals (`sin` is 2 ulp); **nothing** for tensor-core accumulation. The only
  formal artifact is an SMT model of tensor-core `mma` (NFM 2025, arXiv:2502.15999) —
  reverse-engineered, empirically validated, ≤ Ampere, and not a proof the hardware satisfies it.
  No public formal verification of any NVIDIA FPU exists (contrast Centaur x86 FMA in ACL2,
  CPP 2020).

**Blunt:** you cannot prove today that a specific CUDA kernel compiled and run on a real H100
computes a mathematically correct result. Relative to our `native_decide`/GMP common-mode analysis,
a GPU-computed certificate is strictly *worse*: GPU floating point is non-deterministic by explicit
vendor policy, and `ptxas` is unverified with wrong-value bugs on record.

## 2.3 State of the PTX formalization in `SparkInterval/PTX/`

**Better than I expected on rigor, far narrower than CompCert on scope.**

**Size and proof density.** `/home/gersh/gpu_prover/SparkInterval/PTX/` is 34 files, **13,177
lines**, plus `GeneratePTX.lean` (86 lines). Census: 331 `theorem`, 217 `def`, 31
`noncomputable def`, 33 `structure`, 20 `inductive`. **Zero sorries, zero axioms, zero
`native_decide`, zero `opaque`, zero `unsafe`** — the bare string `sorry` does not appear even in
comments. All 34 `.olean` files are present, so the kernel has actually checked them. There is
machine-checked axiom-audit tooling (`SparkInterval/Audit/TrustedComputeCertificates.lean:1-135`,
`#audit certificates` via `Lean.collectAxioms`). The repo's **one** project axiom is not in the PTX
layer at all — it is the execution-boundary axiom
`accepted_run_certificate_sound` (`SparkInterval/Execution/Trusted/RunCertificate.lean:36`).

**What is modelled.** `SparkInterval/PTX/AST.lean:70-96` defines 24 typed instruction constructors;
`:146-151` a closed 26-opcode allowlist.
- Types: **`f64` only** for floating point, plus `pred`, byte, `u32`, `u64` (`AST.lean:18-24`).
  No f32, f16/bf16, vectors, or tensor types.
- Float ops: `add/sub/mul` in **`.rm`/`.rp` only** (directed rounding — exactly right for interval
  arithmetic), plus `min.f64`/`max.f64`. **No `.rn`, no `.rz`, no `fma`, no division** —
  `NvidiaPTXSpec.lean:276-288` proves `currentOpcode_has_no_division_clause`.
- Float domain: `F64Value = negInf | finite ℝ | posInf`. **Numerical, not bit-exact**: finite
  binary64 values are their exact reals, signed zeros identified, **NaN not representable at all**
  (`MachineSemantics.lean:12-17`).
- Memory: a logical model — `GlobalMemory` is two partial maps (`Nat → Option F64Value` and
  `Nat → Option (Fin 256)`) sharing byte addresses, so **f64 cells and bytes cannot alias by
  construction**; `loadByte_storeF64` is `rfl` (`:100-103`). Real byte/word aliasing is assumed
  away. Input/output non-aliasing is a *hypothesis* (`SafeKernelLayout`, `:434-444`).
- Threads: **essentially none.** `ThreadContext` is three naturals (`ctaidX, ntidX, tidX`,
  `:119-122`) — **one logical thread in isolation.** No warps, scheduling, `bar.sync`, shared
  memory, atomics, divergence/reconvergence, or cross-thread noninterference.
  `docs/GPU_MODEL.md:123-125` states it: *"This is a one-thread modeled theorem. It does not prove
  grid coverage, cross-thread noninterference, CUDA scheduling, or physical execution."*
- Control flow: **real** — `pc`, label resolution, predicated and unconditional `bra`, `ret`,
  fuel-bounded `run` (`:185-196, 300-324, 365-380`), plus a structured `executeCode` with
  `CodeControl = fallthrough | jump | returned` for compositional induction (`:329-362`).

**Is there a semantics-preservation theorem? Yes — three real ones.**
- `StructuralCompilerCorrect.lean:883-887`: `buildModule_eq_expectedModule` — production
  `buildModule` proved equal, operand-for-operand, to an independently written structural spec.
- `GeneratedKernelRunRefinement.lean:32-49`: `runBuildModule_inRange` — a whole-module operational
  refinement from source evaluation to `run` on the modelled machine, with layout and thread-safety
  hypotheses.
- `GeneratedKernelRunRefinement.lean:314-331`: concludes `observed.interval.ContainsReal value`
  from `batch.expression.Realizes realEnvironment value` — a genuine source-to-machine containment
  theorem.

**Where it is thin.** `NvidiaPTXSpec.lean` is mostly a **citation table** — 35 `Clause` constructors
mapping opcodes to section anchors in a SHA-256-pinned PTX ISA 9.0 PDF (`:40-50`). The conformance
theorems over it are near-vacuous:

```lean
theorem allowedOpcode_has_pinned_clause {opcode : Opcode}
    (_hopcode : opcode ∈ allowedOpcodes) :
    ∃ clause, opcodeClause opcode = clause ∧ clause.reference.source = sourcePin := by
  exact ⟨opcodeClause opcode, rfl, Clause.reference_source _⟩
```

"Every opcode has a citation," proved by `rfl`. Zero semantic content. The only *semantic* NVIDIA
content is `evalFinite` (`:320-324`) and `minimum`/`maximum` (`:361-374`) — a hand transcription of
the prose for **finite-operand** `add/sub/mul.rm/rp.f64` and non-NaN `min/max`, matched to the
machine model in `NvidiaPTXRefinement.lean:69-128`. Its own docstring is candid (`:130-135`):
*"It does not give semantics to the structural, memory, or control opcodes, does not prove that
rendered instruction text has the cited meaning, and is not a PTX, toolchain, SASS, driver, or
hardware conformance theorem."* **Faithfulness of the transcription to the NVIDIA PDF is a human
review obligation, not a proof.**

**The last mile is a `printf`.** `GeneratePTX.lean` is 86 lines of CLI plumbing. The emission itself
is `renderUncheckedFor` (`Emitter.lean:214-237`) → a `String`, via `renderInstruction`
(`:62-108`) using `s!"..."` interpolation. **There is no parser and no round-trip theorem.**
A typo writing `mul.rn.f64` where the AST says `.rm` would be **completely invisible to every Lean
proof**. `docs/GPU_MODEL.md:31` names the row exactly: *"Emitted PTX text | Deterministic rendering
of the same validated AST | No operational text parser/refinement back to the machine."*
That gap is currently plugged by a golden SHA-256 test and grep-level negative checks
(`assertNotIn(".rn.f64")`, `assertNotIn("fma.")`, `tests/test_ptx_generator.py:206-225`), plus
`ptxas` assembly for sm_121/sm_90 that is **silently skipped if `ptxas` is absent** (`:151-157`),
an `nvdisasm` SASS opcode census (`tools/inspect_generated_sass.py`), and differential conformance
against exact rational Python via the CUDA Driver API (`tools/run_generated_ptx_conformance.py`).
All testing, none of it proof.

There is also a 243-line SASS slice (`SparkInterval/SASS/SM90DirectedAdd.lean`, 0 sorries)
modelling exactly two instructions (`DADD.RM`, `DADD.RP`), whose header disclaims being a SASS
semantics, a `ptxas` proof, or a hardware conformance theorem (`:19-23`).

**What the docs say the GPU is trusted for** (`docs/TRUST_MODEL.md:244-277`, verbatim):

> The trusted computing base for interpreting an actual DGX run as an instance of that theorem
> still includes: the reviewed prose-to-Lean transcription and all PTX behavior outside its
> finite/non-NaN arithmetic slice; the connection between complete emitted PTX instruction text
> and that partial formal semantics; `ptxas` translation and the relationship between PTX and
> SASS; the CUDA loader, driver, and scheduling behavior; GPU arithmetic, memory, and control-flow
> hardware; the host runner, operating system, storage, and artifact collection; and the relevant
> hashing and serialization implementations.
> **Static PTX/SASS audits and differential tests provide useful evidence about this boundary,
> but they are not refinement proofs.**

And `docs/ARCHITECTURE_EXECUTION_BOUNDARY.md:110-126`: *"Until those proofs exist, an attestation
can authenticate a measured run but cannot establish PTX-to-SASS or hardware semantic
conformance."*

**How far would it have to go?** Four axes, each large:

1. **Source language.** CompCert compiles Clight. This compiles a polynomial expression AST
   (constants, variables, negate, `+`, `−`, `×`, `pow`). No division, loops, functions, pointers,
   or conditionals in the source. **Platt's method needs division, `exp`, `log`, `sin`/`cos`,
   `lgamma`, and an FFT with a nontrivial loop nest.** Adding directed division alone is called
   out as absent (`ZETA_ZERO_VERIFIER.md:549`).
2. **Target coverage.** 26 opcodes, semantic refinement for 6 of them. Every load, store, address
   computation, conversion, predicate, and branch has a model and a citation but no argued
   correspondence to NVIDIA's document.
3. **The string gap.** Needs a PTX text parser and a round-trip theorem. Tractable — probably the
   single highest-value item — but not done.
4. **Concurrency.** A one-thread model with no warps, scheduling, divergence, or noninterference
   is missing the thing that makes GPUs hard. Grid coverage is not addressed at all.

And past all four sits `ptxas`, which is closed and unverifiable, and the hardware, for which the
only public conformance evidence includes known violations.

**Fair characterization:** a well-executed, fully-proved, deliberately narrow verified compiler for
interval-polynomial kernels, whose theorem ends one layer above the artifact and several layers
above the hardware. Read it as **narrowing the trusted base**, not as a semantics-preservation
story for GPU execution. Anyone calling it "formally verified GPU code" would be overclaiming, and
the repo's own docs would contradict them.

## 2.4 The checker/prover asymmetry — the most promising direction, and its current problem

**This is already the repo's architecture, and roughly half of it is built.** Assessment, honestly:

### What exists and works

**Sign-change bracket checking, fully proved in Lean, kernel-reducible, no `native_decide`**
(`docs/algorithms/ZETA_ZERO_VERIFIER.md:166-180`):

> "A rational bracket records exact rational endpoints and rational enclosures of the evaluator at
> both endpoints. The kernel-reducible Boolean checker validates each bracket and compares only
> consecutive brackets: for `n` entries it performs `n - 1` adjacent-order comparisons rather than
> an all-pairs separation scan. … It rejects decreasing endpoints, malformed enclosures,
> zero-containing results, equal signs, and overlapping or misordered families. Thus sign and
> ordering decisions require neither `native_decide` nor trusted floating-point comparisons."

**The finite arithmetic of Turing's method, proved in Lean, no axioms.**
`SparkInterval/Zeta/TuringWindowCertificate.lean:9-19` reproduces Platt's `zeta_arb/turing.c`:

```
C       = (-(a+b) log(pi) (b-a) / 4 + ImGammaIntegral) / pi
qUpper  = ( SBound - NrightIntegral + C) / (b-a)
qLower  = (-SBound - NleftIntegral  + C) / (b-a)
maxN    = floor(qUpper) + 1
minN    = ceil(qLower)  + 1
```

Inputs (`:54-71`): rational `a`, `b`, spacing `delta` (21/512 in PT21), `RatInterval` enclosures of
`sBound = 0.059·log t + 2.067`, `logPi`, `imGammaIntegral`, `pi`, and two integer weights from
`Nleft_int`/`Nright_int`. Cost on the trusted side is trivial: a handful of exact-rational interval
ops plus floor/ceil comparisons per window (measured proxy: the directed-Arb Turing step is
**0.00034 s per PT21 block**, `PLATT_PT21_FUSED_EVENT_STREAM.md:213-214`).
`exact_endpoint_counts` then proves `countAtLeft = lowerCount ∧ countAtRight = upperCount ∧
countAtLeft + isolatedCount = countAtRight` **with no simplicity assumption**.

**A working end-to-end asymmetric loop, at toy scale.** `tools/generate_grh_lean.py` converts a
certificate for modulus 3 or 4 into a Lean file that kernel-checks the bracket family and states
the conditional finite-strip GRH theorem, ending in
`theorem grh_modulus_4_finite_verification … : GRHVerifiedForModulus 4 lo hi` with `#print axioms`
reporting only `propext, Classical.choice, Quot.sound` (`docs/algorithms/GRH_POC.md:54-96`).

**The precision asymmetry is real and the code exploits it.** The verifier works in **exact
rationals** and needs only that the producer-supplied endpoint enclosures exclude zero with
opposite signs. Practical widths are ~1e-11 at t≈30 and ~1e-8 at t≈2000 (`GRH_POC.md:181-183`) —
far coarser than 2⁻¹⁰² ≈ 2e-31 and amply sufficient to see a sign change. Meanwhile the *generator*
uses 300-bit MPFI (Platt), 2176-bit host replay (PT21 scanner), 128/256-bit Turing inputs, 192-bit
Arb (Dirichlet). Platt's ±2⁻¹⁰² enters the trusted side only as **integer arithmetic**:
`SparkInterval/Zeta/LMFDBPrefixBoundary.lean:9-13` doubles the 2⁻¹⁰¹ grid so a midpoint is a
natural at scale 2¹⁰², with integer endpoints `midpoint ± 1`; *"All comparisons with the target
height are integer comparisons at scale `2^102`. No binary64 or host-libm comparison decides the
boundary count"* (`tg_verifier/lmfdb_zeta_prefix.py:15-16`).

**Certificate formats crossing the boundary** are designed and partly built: the PT21 compact block
artifact (`sparkinterval.tg.platt-pt21-lean-block-artifact.v2`, ≤16 MiB, three streams
`main`/`left_flank`/`right_flank`, exact rational endpoints and Turing intervals) with a Lean
consumer `SparkInterval.Zeta.PT21ArtifactBinding.BlockArtifact.check` that **derives** the geometry
rather than trusting it (block `k` is `[10^10 + 1008k, 10^10 + 1008(k+1)]`, offsets `a + 504 + j·21/512`).

### Why it does not currently work at scale — four blockers

**(1) No Hardy Z in Lean.** `ZETA_ZERO_VERIFIER.md:9-13`: the implementation *"does **not** yet
define a concrete Hardy Z, evaluate the Riemann-Siegel formula, certify transcendental functions,
or prove a Turing or argument-principle count."* Nothing identifies Arb's Hardy function with
Mathlib's `riemannZeta`. **This is the load-bearing gap** — without it, a verified bracket family
proves nothing about `riemannZeta`.

**(2) No formal Turing / argument-principle theorem.** `AnalyticTuringBounds`
(`TuringWindowCertificate.lean:391-397`), `LZeroCountUpperBound`, and
`ZetaMultiplicityCountUpperBound` are all *hypotheses you must supply*. The Dirichlet side is
Python-only (`tg_verifier/dirichlet_postprocess.py::paired_turing`) and lists **eight numbered Lean
obligations** before `production_accept` can flip
(`DIRICHLET_TURING_REFLECTED_BOUND.md:361-413`).

**(3) The trusted side is currently *slower* than the untrusted side.** This is the finding that
most undercuts the hope. Every measured checker in the repo is between 0.4× and 3× the cost of the
generator — **except the Lean kernel, which is ~10⁴× worse** (`GRH_POC_BENCHMARKS.md:137-141`):

> "the kernel-mode checker verified 122 brackets in 5.6 s (~22 brackets/s single-threaded,
> including ~5 s fixed elaboration overhead); at that rate the full 3.8e13-zero certificate would
> be a CPU-cluster-scale verification (~5e4 core-years)"

Supporting numbers: exact CPU replay of GPU rows runs at ~6,060 rows/s vs 9.76e8 GPU term-evals/s
(`:47, :104`); the Dirichlet direct-fallback checker costs **as much as the producer** (88.04 s
producer+checker vs 44.48 s producer alone, `DIRICHLET_ZERO_CLOSURE_STAGE.md:161-162`); the Python
record adapter is 2.7× *slower* than the GPU generator (`PLATT_PT21_NATIVE_FINALIZER.md:231-236`).
The repo itself identifies the fix (`GRH_POC_BENCHMARKS.md:141-146`): a streaming checker *"plus
compiled (`native_decide`-class or extracted-checker) verification would be required for the formal
side to keep pace with the GPU side."*

**(4) The certificate is inherently linear in the zero count.**
`ZETA_ZERO_VERIFIER.md:565-575`: *"A certificate containing one explicit bracket per zero is
therefore inherently linear in that count."* And `:605-609`: *"A Merkle root by itself proves only
integrity of later-opened chunks… A truly small independently verifiable download would require
either a substantially more compressed analytic certificate or a sound succinct-proof system;
neither exists in this repository."* For zeta that is 1.24e13 brackets; for Dirichlet ~1e14.
Storage scale in the repo: all `PT21EVT1` event records = 530 GiB retained; the full `PT21SGN1`
sign packets would be **1.8428 PB**, which the fused stage therefore retains none of
(`PLATT_PT21_FUSED_EVENT_STREAM.md:175-181`).

### Honest assessment of the direction

The asymmetry is **mathematically real** — checking a sign change at a given rational point needs
~50 bits and no transcendentals, while finding the zero needs 300 bits and an FFT — and the repo
has already isolated it correctly (`n−1` exact-rational comparisons per bracket family). It is
**not currently realized in engineering**: the only implementation runs through Lean elaboration at
22 brackets/s.

If one wanted to pursue it, the tractable path is visible and does not involve GPUs at all:

1. Prove Hardy Z in Lean and its zero correspondence with `riemannZeta` (**the hard, mathematical,
   irreducible item**).
2. Prove the Turing / argument-principle inequality (second hard item; the Dirichlet variant has a
   documented eight-step obligation list, and Platt's printed Theorem 3.2 has a numerically refuted
   term plus an `im_int2` code bug that must be repaired first).
3. Replace the Lean-elaboration bracket checker with an extracted or `native_decide`-class compiled
   checker — a ~10⁴× engineering win, and the only step where the certificate size becomes tolerable.
4. Only then does the witness generator matter, and at that point it can be *anything*, including a
   completely untrusted GPU — which is precisely the point of the design.

Note the ordering: **the GPU is the last item, not the first.** Steps 1 and 2 are pure formalization
and are what actually block discharge. Step 3 is CPU engineering. Nothing on that list is made
easier by buying H100 time.

---

# Conclusion

**Half one.** GPUs help, by roughly 50–90× per device over one CPU core (measured on GB10), with a
projected further ~70× from GB10 to H100 on the DP-issue-bound kernel — better than the repo's own
14.3× bandwidth-roofline tables suggest. Best case for the zeta axiom's FFT+Taylor stages is
~$1.8k–$9k on 8 confidential H100s over ~6.7 days at the still-current $1.419/GPU-hour Azure spot
price. But this matters much less than it appears, because **the honest CPU cost is 4.4–7.5 million
core-hours (~$37k–$63k spot), not 6.8e5 core-years.** The $30M figure comes from benchmarking the
per-zero isolator instead of Platt's windowed multi-evaluation — a ~500–1300× algorithmic gap. The
Dirichlet axiom has no defensible ETA at all and has documented defects in its *source literature*
that must be fixed before any computation could be correctly specified.

**Half two.** An H100 CC attestation covers GPU firmware and nothing else — not the cubin, not
memory, not the result — and NVIDIA explicitly disclaims even determinism of the arithmetic. It was
relay-attacked in 2025 against Phala's exact stack. No CompCert-equivalent exists for CUDA/PTX/SASS
and none is in progress; `ptxas` is a closed binary with confirmed wrong-value bugs. The repo's PTX
formalization is genuine, sorry-free, kernel-checked work with real refinement theorems, but it
covers 26 opcodes, one thread, no NaN, no division, no transcendentals, and it terminates at a Lean
inductive whose rendering to text is an unverified `printf`. Getting from there to a
CompCert-grade GPU story requires a source language with transcendentals, semantic refinement for
~20 more opcodes, a PTX text parser and round-trip theorem, a concurrency model — and then still
hits `ptxas`, which cannot be verified from outside NVIDIA.

**The checker/prover asymmetry is the right answer and the repo already knows it.** But it relocates
the problem rather than solving it: the trusted side today is 10⁴× slower than the untrusted side,
and the two genuinely blocking items — a Lean Hardy Z tied to `riemannZeta`, and a formal
Turing/argument-principle count — are mathematics, not hardware.

**So, plainly: these two axioms stay cited regardless of hardware.** Not because the computation is
unaffordable (it is affordable, and cheaper than assumed), but because there is no formal statement
in Lean for a certificate to discharge into, no verified path from any GPU to any claim, and a
per-zero certificate of 10¹³–10¹⁴ brackets that the only axiom-free checker processes at 22/s.
Buying GPU time changes none of those four facts. If effort is to be spent, spend it on Hardy Z and
the Turing bound in Lean, and on a compiled certificate checker — in that order, and on CPUs.

---

## Corrections to the brief

- **`tools/benchmark_tg_platt_pt21_native_artifact_builder.py` is not on `main`.** It exists only
  on `agent/compcert-tdx-attestation` (194 lines, in the `/home/gersh/gpu_prover_wt_phala`
  worktree). On `main` the only PT21 benchmark tools are
  `tools/benchmark_tg_platt_pt21_native_record_adapter.py` and
  `tools/benchmark_tg_platt_pt21_native_scan_fastpath.py`, both CPU-side Python adapter
  benchmarks, not GPU.
- **"~6e13 zeros (Dirichlet)"** — no such figure exists anywhere in `gpu_prover`; the Dirichlet
  workload is only ever quantified in characters and butterflies. My independent estimate is
  ~1e14 for `|Im ρ| ≤ T₀`, ~5e13 one-sided; the brief's figure is consistent one-sided.
- **"~6.8e5 core-years for the first"** — correct for the algorithm measured, but that algorithm
  is ~500–1300× slower than Platt's own. See §1.1.
- **"$1.419/GPU-hour confidential H100 spot"** — verified still current on 2026-07-30 via the
  Azure Retail Prices API, East US 2, meter expiring 2026-07-31.

## Appendix: derived arithmetic

All from `PLATT_PT21_WINDOWED_SOURCE_CAMPAIGN.md:104-153` and the brief's Arb measurements.

```
blocks                       = 2,966,443,783            (1e10 -> 3,000,175,333,264, step 1008)
zeros                        = 12,363,153,437,138       (N(3000175332800))
zeros/block                  = 4,167.7
CPU  5.37875 s/block         -> 1.29 ms/zero            -> 4.432e6 core-hours = 506 core-years
Platt-Trudgian published                                   7.5e6  core-hours = 856 core-years
Arb isolator (brief's fit, integrated to 1.2363e13)     -> 4.13e9 core-hours = 4.7e5 core-years
algorithmic ratio at index 1e12                         = 659 ms / 1.29 ms   = 511x

Azure DC96as_v6 ($4.358 PAYG / $0.805358 spot per 96-core node-hour):
  4.432e6 core-hours -> $201,201 PAYG / $37,182 spot
  7.5e6   core-hours -> $340,469 PAYG / $62,919 spot

GB10 measured 9.2043 windows/s  vs  1 ARM core 0.1859 blocks/s  ->  49.5x
GB10 optimized 16.46 windows/s                                  ->  88.5x
H100 34 TFLOP/s FP64 / GB10 0.49 TFLOP/s                        ->  ~70x  (repo tables used 14.3x)
8 x H100 @ 70x:  1,280 node-hours, 6.66 days,  $1,816 spot / $8,931 PAYG   (FFT+Taylor only)
Repo's honest 2-stage 16-node shape at 7 days:  $18,762 PAYG / $3,814 spot (all stages)

Dirichlet Thm 7.1, my totient-sieve estimate, |Im rho| <= T0(q), q <= 400000:
  ~1.6e14 using phi(q) as char count; ~1e14 correcting to primitive chars
  = 8-13x the zeta workload.  Repo has no ETA for it.
```
