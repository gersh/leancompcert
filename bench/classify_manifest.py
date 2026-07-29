#!/usr/bin/env python3
"""Classify every one of claude_math's 1371 `native_decide` atoms by the SHAPE
and SCALE of the finite computation it discharges.

Input : /home/gersh/claude_math/problems/ternary-goldbach/native_decide_manifest.json
        (read-only; the manifest records each atom's exact decided proposition)
Output: bench/results/native_decide_shapes.csv   (one row per atom)
        bench/results/native_decide_shapes.json  (per-shape aggregate)

Scale is reported as `primitive_ops`: the number of *primitive kernel
reduction units* the computation costs, where one unit is one fold/recursion
step of the shape's inner loop.  Where the shape is a transcendental-enclosure
tree the unit is one `RatInterval` node evaluation, and `bignum_bits` records
the operand width, because bignum width -- not step count -- is what dominates
those.

The per-kernel cost models come from reading the definitions in claude_math
(see the report for file:line references); the *counts* come from the manifest.
"""
import csv, json, os, re, sys

sys.set_int_max_str_digits(200000)
from collections import Counter, defaultdict

MANIFEST = ("/home/gersh/claude_math/problems/ternary-goldbach/"
            "native_decide_manifest.json")
OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                   "bench", "results")

PROJ = re.compile(r"^(MathExtras|AnalyticNT|Math\.|IntervalArith|"
                  r"TGNativeCertificates|HelfgottCertificates)")

# ---------------------------------------------------------------------------
# Shape catalogue.  key = a project constant that identifies the shape;
# value = (shape_class, arithmetic_domain, note)
#
# shape_class values:
#   transcendental-enclosure : fixed-term Taylor/series in exact Rat, operand
#                              width set by the argument, no rounding
#   bisection-tree           : 2^depth (or pruned) interval-tree evaluations
#   linear-fold-nat          : tail recursion over a range, fixed-width Nat
#   linear-fold-rat          : tail recursion over a range, exact Rat (growing)
#   linear-fold-sieve        : as above but each step needs minFac/Prime/
#                              Squarefree (~sqrt(n) trial divisions)
#   table-streaming          : materializes an Array of length `bound` first
#   fixed-expression         : constant-depth arithmetic, no loop
# ---------------------------------------------------------------------------
SHAPES = {
  "IntervalArith.RatInterval.log_enclose_full":
      ("transcendental-enclosure", "Rat (exact, unbounded)",
       "24-term Mercator series + ~log2(x) halving reduction; no rounding"),
  "IntervalArith.RatInterval.exp_enclose":
      ("transcendental-enclosure", "Rat (exact, unbounded)",
       "N-term Taylor then interval pow by 2^D -- 4*2^D Rat mults, linear digit growth"),
  "IntervalArith.RatInterval.interval_bisect":
      ("bisection-tree", "Rat/RatInterval",
       "unconditional 2^depth leaf evaluations"),
  "IntervalArith.RatInterval.adaptiveUpper":
      ("bisection-tree", "Rat/RatInterval",
       "pruned binary bisection, worst case 2^(fuel+1)-1 leaf evaluations"),
  "MathExtras.RS62Ladder.loopE":
      ("linear-fold-sieve", "Nat (<= 2^63 fixed point)",
       "one Nat.minFac primality test per step (~sqrt(n)/2 divisions)"),
  "MathExtras.RS62Ladder.loop410":
      ("linear-fold-sieve", "Nat (2^48 fixed point)", "as loopE plus a window check"),
  "MathExtras.RS62Ladder.loop314":
      ("linear-fold-sieve", "Nat (2^48 fixed point)", "as loopE plus eq-(3.14) window"),
  "MathExtras.RS62MertensFirst.loop":
      ("linear-fold-sieve", "Nat (2^48 fixed point)", "four fixed-point accumulators"),
  "MathExtras.Helfgott1221.checkAll":
      ("linear-fold-rat", "Rat (exact product, growing)",
       "per q: exact product over primes<=m plus two log series"),
  "MathExtras.Helfgott.CorC13Certificate.corC13MarginKernel":
      ("bisection-tree", "RatInterval, roundOut 2^48",
       "k-term Lambda*eta2 sum per bisection cell; denominators pinned"),
  "MathExtras.Helfgott.MinorSection51Pieces.BandIntervalExpr.evalInterval":
      ("bisection-tree", "RatInterval (exp/log/sqrt nodes, no rounding)",
       "20-40 transcendental nodes per cell, no subtree sharing"),
  "AnalyticNT.LargeSieve.uFold":
      ("linear-fold-nat", "Nat", "pure Nat accumulation"),
  "AnalyticNT.LargeSieve.gSum":
      ("linear-fold-sieve", "Nat", "squarefree factorization per step"),
  "AnalyticNT.LargeSieve.gFold":
      ("linear-fold-sieve", "Nat + one Rat compare/step", "10^5 steps"),
  "AnalyticNT.LargeSieve.gFold1215":
      ("linear-fold-sieve", "Nat + Rat Pade log (m^16)", "10^7 steps"),
  "AnalyticNT.LargeSieve.cePrimeAux":
      ("linear-fold-rat", "Rat with p^48", "sup over 96 Rat candidates per prime"),
  "AnalyticNT.LargeSieve.ceUPrimeAux":
      ("linear-fold-rat", "Rat with p^48", "inf over 96 Rat candidates per prime"),
  "AnalyticNT.ChebyshevPsi.checkAllPsiLeMul":
      ("linear-fold-sieve", "Nat (2^40 fixed point)", "IsPrimePow + minFac per step"),
  "AnalyticNT.ChebyshevPsi.checkAllPsiSubThetaLeSqrt":
      ("linear-fold-sieve", "Nat (2^40 fixed point)", "IsPrimePow + minFac per step"),
  "AnalyticNT.ChebyshevPsi.checkPsiLeMulFrom":
      ("linear-fold-sieve", "Nat (2^40 fixed point)", "plus a `lower`-length seed sum"),
  "TGNativeCertificates.Ramare.Finite100M.checkFirstMertens100M":
      ("table-streaming", "Nat (2^48 fixed point)", "Array Nat of length 10^8"),
  "TGNativeCertificates.Ramare.Lemma71.checkLemma71_100M":
      ("table-streaming", "Nat/Int (2^48)", "Array Nat of length 10^8"),
  "TGNativeCertificates.Ramare.MStar140MEngine.checkLimit":
      ("table-streaming", "Nat/Int (2^48)", "four Arrays of length 1.4*10^8"),
  "TGNativeCertificates.CDEMMertens.rangeSweep":
      ("linear-fold-sieve", "Int (|M| < 1000)", "mu per step"),
  "TGNativeCertificates.CDEMTablePrefixEngine.checkPrefixFields":
      ("linear-fold-rat", "Int/Nat at 10^30", "five folds over d <= 199330"),
  "TGNativeCertificates.PrimeLogSquare219.checkPrimeLogSquareTable":
      ("table-streaming", "Nat", "factorTable bound + five log/prefix states"),
  "TGNativeCertificates.WeightedMoment217.checkWeightedMomentTable":
      ("table-streaming", "Nat (acc ~ 2^110)", "factorTable 1.9*10^7"),
  "MathExtras.LiouvilleSweep.ladderRun":
      ("linear-fold-sieve", "Int (<= 2^50)", "65 bands, lambda per step"),
  "MathExtras.LiouvilleSweep.bandRun":
      ("linear-fold-sieve", "Int (<= 2^50)", "lambda per step"),
  "MathExtras.NumberTheory.Mertens.LittleRamareFinite.ladderRun":
      ("linear-fold-sieve", "Int (<= 2^50)", "10 bands, mu per step"),
  "MathExtras.NumberTheory.Mertens.LittleRamareFinite.bandRun":
      ("linear-fold-sieve", "Int (<= 2^50)", "mu per step"),
  "MathExtras.EffectiveMertensDecay.littleLvalF":
      ("linear-fold-nat", "Int (<= 2^50)",
       "QUADRATIC: O(U) per call, called once per n in [3,11817]"),
  "MathExtras.Helfgott.Section24.Head30000.scan":
      ("linear-fold-rat", "RatInterval, wround pinned",
       "NON-TAIL recursion, 30000 levels deep"),
  "MathExtras.Helfgott.EtaPlusHDerivGridCert.check":
      ("linear-fold-nat", "Nat (10^12 fixed point)", "200000 steps, degree-4 poly"),
  "MathExtras.HelfgottLargeQ.masterCheck":
      ("fixed-expression", "Rat", "112 leaves; already kernel-decided upstream"),
  "MathExtras.NumberTheory.Analysis.MV73Lemma7Floor.certFrom":
      ("linear-fold-rat", "Rat (denominator = lcm of phi(r), grows)",
       "exact rational Mertens-type sum"),
  "MathExtras.NumberTheory.Analysis.MV73WeightedFloorSevenTwentieths.passC":
      ("linear-fold-rat", "Rat (1000-term exact sum)", "~995 grid cells"),
  "MathExtras.NumberTheory.Analysis.MV73WeightedFloorSevenTwentieths.passD":
      ("linear-fold-rat", "Rat (1000-term exact sum)", "~1003 grid cells"),
  "MathExtras.NumberTheory.Helfgott.AppendixACertificates.bandEval":
      ("bisection-tree", "CInterval, roundOutC 2^120",
       "K^2 complex mults per cell; bisection fuel 34"),
  "MathExtras.NumberTheory.Helfgott.AppendixACertificates.momentEval":
      ("fixed-expression", "CInterval, roundOutC 2^120", "linear K-step series"),
  "MathExtras.NumberTheory.Helfgott.AppendixA5Certificates.numEval":
      ("bisection-tree", "CInterval, roundOutC 2^120", "bisection fuel 20"),
  "MathExtras.NumberTheory.Helfgott.AppendixA5Certificates.numMomentEval":
      ("fixed-expression", "CInterval, roundOutC 2^120", "fixed 120-step series"),
  "Math.Problems.TernaryGoldbach.oddMertensLoAcc":
      ("linear-fold-sieve", "Nat (2^64)", "150k Squarefree decisions + totient"),
  "Math.Problems.TernaryGoldbach.oddMertensHiAcc":
      ("linear-fold-sieve", "Nat (2^64)", "150k Squarefree decisions + totient"),
  "Math.Problems.TernaryGoldbach.gcdMertensHiAcc":
      ("linear-fold-sieve", "Nat (2^64)", "150k Squarefree decisions + gcd"),
  "Math.Problems.TernaryGoldbach.phiSqHiAcc":
      ("linear-fold-sieve", "Nat (2^64)", "150k Squarefree decisions"),
  "Math.Problems.TernaryGoldbach.phiSqDiscHiAcc":
      ("linear-fold-sieve", "Nat (2^64)", "150k Squarefree decisions + Nat.sqrt"),
  "Math.Problems.TernaryGoldbach.quinticMertensHiAcc":
      ("linear-fold-sieve", "Nat (2^64)", "150k Squarefree decisions"),
  "Math.Problems.TernaryGoldbach.deficitCertAcc":
      ("linear-fold-sieve", "Nat (2^64)", "2*10^6 Nat.Prime decisions"),
  "Math.Problems.TernaryGoldbach.HEnvFloorCert.segProp":
      ("transcendental-enclosure", "Rat (exact)",
       "92 segments x (1 log prec-40 + 3 exp prec-30, one with D=8 => 256-fold pow)"),
}

# Known iteration counts / bisection depths, read off the call sites.
# (kernel-name -> primitive step count for the *whole atom*)
KNOWN_STEPS = {
  "MathExtras.RS62Ladder.loopE": 99999900,
  "MathExtras.RS62Ladder.loop410": 99900010,
  "MathExtras.RS62Ladder.loop314": 14497998,
  "AnalyticNT.ChebyshevPsi.checkAllPsiLeMul": 10000000,
  "AnalyticNT.ChebyshevPsi.checkAllPsiSubThetaLeSqrt": 1000000,
  "AnalyticNT.ChebyshevPsi.checkPsiLeMulFrom": 4000000,
  "AnalyticNT.LargeSieve.gFold": 100000,
  "AnalyticNT.LargeSieve.gFold1215": 10000000,
  "TGNativeCertificates.Ramare.Finite100M.checkFirstMertens100M": 100000000,
  "TGNativeCertificates.Ramare.Lemma71.checkLemma71_100M": 100000000,
  "TGNativeCertificates.Ramare.MStar140MEngine.checkLimit": 140000000,
  "TGNativeCertificates.CDEMTablePrefixEngine.checkPrefixFields": 996650,
  "TGNativeCertificates.WeightedMoment217.checkWeightedMomentTable": 19000000,
  "MathExtras.EffectiveMertensDecay.littleLvalF": 70000000,
  "MathExtras.Helfgott.Section24.Head30000.scan": 30000,
  "MathExtras.Helfgott.EtaPlusHDerivGridCert.check": 200000,
  "MathExtras.LiouvilleSweep.ladderRun": 4000000,
  "MathExtras.NumberTheory.Mertens.LittleRamareFinite.ladderRun": 20953,
  "Math.Problems.TernaryGoldbach.oddMertensLoAcc": 150000,
  "Math.Problems.TernaryGoldbach.oddMertensHiAcc": 150000,
  "Math.Problems.TernaryGoldbach.gcdMertensHiAcc": 150000,
  "Math.Problems.TernaryGoldbach.phiSqHiAcc": 150000,
  "Math.Problems.TernaryGoldbach.phiSqDiscHiAcc": 150000,
  "Math.Problems.TernaryGoldbach.quinticMertensHiAcc": 150000,
  "Math.Problems.TernaryGoldbach.deficitCertAcc": 2000000,
  "MathExtras.Helfgott1221.checkAll": None,       # from literals
}

# priority: the first match wins as the atom's "primary kernel"
PRIORITY = [
  "TGNativeCertificates.Ramare.MStar140MEngine.checkLimit",
  "TGNativeCertificates.Ramare.Finite100M.checkFirstMertens100M",
  "TGNativeCertificates.Ramare.Lemma71.checkLemma71_100M",
  "TGNativeCertificates.WeightedMoment217.checkWeightedMomentTable",
  "TGNativeCertificates.PrimeLogSquare219.checkPrimeLogSquareTable",
  "TGNativeCertificates.CDEMTablePrefixEngine.checkPrefixFields",
  "TGNativeCertificates.CDEMMertens.rangeSweep",
  "AnalyticNT.ChebyshevPsi.checkAllPsiLeMul",
  "AnalyticNT.ChebyshevPsi.checkAllPsiSubThetaLeSqrt",
  "AnalyticNT.ChebyshevPsi.checkPsiLeMulFrom",
  "AnalyticNT.LargeSieve.gFold1215",
  "AnalyticNT.LargeSieve.gFold",
  "AnalyticNT.LargeSieve.gSum",
  "AnalyticNT.LargeSieve.uFold",
  "AnalyticNT.LargeSieve.cePrimeAux",
  "AnalyticNT.LargeSieve.ceUPrimeAux",
  "MathExtras.RS62Ladder.loopE",
  "MathExtras.RS62Ladder.loop410",
  "MathExtras.RS62Ladder.loop314",
  "MathExtras.RS62MertensFirst.loop",
  "MathExtras.Helfgott1221.checkAll",
  "MathExtras.HelfgottLargeQ.masterCheck",
  "MathExtras.EffectiveMertensDecay.littleLvalF",
  "MathExtras.LiouvilleSweep.ladderRun",
  "MathExtras.LiouvilleSweep.bandRun",
  "MathExtras.NumberTheory.Mertens.LittleRamareFinite.ladderRun",
  "MathExtras.NumberTheory.Mertens.LittleRamareFinite.bandRun",
  "MathExtras.Helfgott.Section24.Head30000.scan",
  "MathExtras.Helfgott.EtaPlusHDerivGridCert.check",
  "MathExtras.NumberTheory.Analysis.MV73Lemma7Floor.certFrom",
  "MathExtras.NumberTheory.Analysis.MV73WeightedFloorSevenTwentieths.passC",
  "MathExtras.NumberTheory.Analysis.MV73WeightedFloorSevenTwentieths.passD",
  "MathExtras.NumberTheory.Helfgott.AppendixACertificates.bandEval",
  "MathExtras.NumberTheory.Helfgott.AppendixACertificates.momentEval",
  "MathExtras.NumberTheory.Helfgott.AppendixA5Certificates.numEval",
  "MathExtras.NumberTheory.Helfgott.AppendixA5Certificates.numMomentEval",
  "Math.Problems.TernaryGoldbach.oddMertensLoAcc",
  "Math.Problems.TernaryGoldbach.oddMertensHiAcc",
  "Math.Problems.TernaryGoldbach.gcdMertensHiAcc",
  "Math.Problems.TernaryGoldbach.phiSqHiAcc",
  "Math.Problems.TernaryGoldbach.phiSqDiscHiAcc",
  "Math.Problems.TernaryGoldbach.quinticMertensHiAcc",
  "Math.Problems.TernaryGoldbach.deficitCertAcc",
  "Math.Problems.TernaryGoldbach.HEnvFloorCert.segProp",
  "MathExtras.Helfgott.CorC13Certificate.corC13MarginKernel",
  "MathExtras.Helfgott.MinorSection51Pieces.BandIntervalExpr.evalInterval",
  "IntervalArith.RatInterval.exp_enclose",
  "IntervalArith.RatInterval.log_enclose_full",
  "IntervalArith.RatInterval.adaptiveUpper",
  "IntervalArith.RatInterval.interval_bisect",
]

# Band-certificate families: the SII/band `...At` kernels all funnel into
# `adaptiveUpper` over `BandIntervalExpr.evalInterval`; record their depths.
BAND_AT = re.compile(r"MathExtras\.Helfgott\.MinorSection51Pieces\."
                     r"band\w*(?:CertificateAt|SafeAt)")
BAND_DEPTHS = {"high": 7, "medium": 5, "small": 16}


def nat_lits(text):
    """Literal values, plus their decimal widths (the widths are what matter
    for the bignum-dominated shapes and some literals are 40,000 digits)."""
    strs = re.findall(r"nat_lit\s+(\d+)", text)
    return [int(x) for x in strs if len(x) <= 30], \
           (max((len(x) for x in strs), default=0))


def normalize(prop):
    """Collapse the rendered numeral spellings into `LIT{n}` tokens so that
    positional argument extraction is reliable:
      @OfNat.ofNat.{0} Nat (nat_lit N) (instOfNatNat (nat_lit N))  ->  LIT{N}
      @HPow.hPow ... LIT{a} LIT{b}                                 ->  LIT{a**b}
    """
    t = re.sub(r"\s+", " ", prop)
    t = re.sub(r"@OfNat\.ofNat\.\{0\} Nat \(nat_lit (\d+)\) "
               r"\((?:instOfNatNat|@Rat\.instOfNat) \(nat_lit \d+\)\)",
               lambda m: "LIT{%s}" % m.group(1), t)
    t = re.sub(r"@OfNat\.ofNat\.\{0\} Rat \(nat_lit (\d+)\) "
               r"\(@Rat\.instOfNat \(nat_lit \d+\)\)",
               lambda m: "LIT{%s}" % m.group(1), t)
    t = re.sub(r"\(LIT\{(\d+)\}\)", lambda m: "LIT{%s}" % m.group(1), t)
    for _ in range(4):
        t2 = re.sub(r"@HPow\.hPow\.\{0, 0, 0\} Nat Nat Nat "
                    r"\(@instHPow\.\{0, 0\} Nat Nat "
                    r"\(@NPow\.toPow\.\{0\} Nat "
                    r"\(@Monoid\.toNPow\.\{0\} Nat Nat\.instMonoid\)\)\) "
                    r"LIT\{(\d{1,9})\} LIT\{(\d{1,3})\}",
                    lambda m: "LIT{%d}" % (int(m.group(1)) ** int(m.group(2))), t)
        if t2 == t:
            break
        t = t2
    return t


def args_after(prop, kernel):
    """The literal values appearing as the immediate arguments of `kernel`, in
    order.  For the fold engines the first is the fuel, i.e. the exact
    iteration count of THIS atom."""
    t = normalize(prop)
    i = t.find(kernel)
    if i < 0:
        return []
    out = []
    for m in re.finditer(r"LIT\{(\d+)\}", t[i + len(kernel):]):
        v = m.group(1)
        if len(v) > 12:
            break
        out.append(int(v))
        if len(out) >= 8:
            break
    return out


# fold engines whose FIRST argument is the fuel (= exact iteration count)
FUEL_FIRST = {
  "MathExtras.RS62Ladder.loopE",
  "MathExtras.RS62Ladder.loop410",
  "MathExtras.RS62Ladder.loop314",
  "MathExtras.RS62MertensFirst.loop",
  "AnalyticNT.LargeSieve.uFold",
  "AnalyticNT.LargeSieve.gSum",
  "AnalyticNT.LargeSieve.gFold",
  "AnalyticNT.LargeSieve.gFold1215",
  "AnalyticNT.LargeSieve.cePrimeAux",
  "AnalyticNT.LargeSieve.ceUPrimeAux",
  "TGNativeCertificates.CDEMMertens.rangeSweep",
}


def classify(entry):
    prop = entry["proposition"]
    consts = set(x for x in re.findall(r"([A-Za-z_][A-Za-z0-9_.']*)", prop)
                 if PROJ.match(x))
    kernel = None
    for k in PRIORITY:
        if k in consts:
            kernel = k
            break
    band = any(BAND_AT.match(c) for c in consts)
    lits, digits = nat_lits(prop)
    maxlit = max(lits) if lits else 0

    if kernel is None and band:
        kernel = "MathExtras.Helfgott.MinorSection51Pieces.BandIntervalExpr.evalInterval"
    if kernel is None:
        # constant-depth rational/interval comparison built out of named
        # repository constants only
        shape, dom, note = ("fixed-expression", "Rat/RatInterval",
                            "constant-depth comparison of named constants")
        steps = 1
    else:
        shape, dom, note = SHAPES.get(
            kernel, ("fixed-expression", "Rat/RatInterval", ""))
        steps = KNOWN_STEPS.get(kernel)

    # --- scale refinement per shape ---------------------------------------
    bignum_bits = None
    if kernel == "IntervalArith.RatInterval.log_enclose_full":
        # prec is the small literal; the huge literal is the argument
        prec = 24
        for v in lits:
            if 8 <= v <= 200:
                prec = v
                break
        # ~2325 halving steps for a 700-digit argument + 24-term series
        halvings = max(1, int(digits * 3.3219))     # log2(10^digits)
        steps = halvings + 24
        # peak operand: u^(prec+1) where u has `digits` digits
        bignum_bits = int(digits * 3.3219 * (prec + 1)) if digits else None
        note = (f"{prec}-term series, ~{halvings} halving steps, "
                f"argument ~{digits} decimal digits")
    elif band:
        depth = 7
        for tag, dep in BAND_DEPTHS.items():
            if any(tag in c.lower() for c in consts):
                depth = dep
                break
        # worst case pruned bisection x ~30 transcendental nodes per cell
        steps = (2 ** (depth + 1) - 1) * 30
        note = (f"adaptiveUpper depth {depth} (worst case {2**(depth+1)-1} "
                f"cells) x ~30 transcendental nodes/cell")
        bignum_bits = 10000
    elif kernel == "MathExtras.Helfgott.CorC13Certificate.corC13MarginKernel":
        depth = 8
        k = max([v for v in lits if v <= 64] or [10])
        steps = (2 ** depth) * k
        note = f"interval_bisect depth<= {depth} x k={k} Lambda terms; roundOut 2^48"
        bignum_bits = 48
    elif kernel in ("MathExtras.NumberTheory.Helfgott.AppendixACertificates.bandEval",
                    "MathExtras.NumberTheory.Helfgott.AppendixA5Certificates.numEval"):
        steps = 200000
        bignum_bits = 120
        note += "; adaptiveUpper fuel 20-34, roundOutC pins denominators at 2^120"
    if kernel in FUEL_FIRST:
        aa = args_after(prop, kernel)
        if aa:
            steps = aa[0]
            note = f"exact fuel from the atom: {aa[0]:,} iterations"
    elif kernel == "MathExtras.Helfgott1221.checkAll":
        steps = max([v for v in lits if v <= 10 ** 7] or [1000]) * 50
        note = "qmax cells x (|S| exact Rat mults + 2 log series)"
    elif kernel == "TGNativeCertificates.PrimeLogSquare219.checkPrimeLogSquareTable":
        steps = max([v for v in lits if v <= 10 ** 9] or [10 ** 7])
    elif kernel == "IntervalArith.RatInterval.exp_enclose":
        # cost is 4*2^D Rat mults with LINEARLY growing digit length, where
        # D = Nat.log2(|x|) + 1; x is the small literal, not the mantissa
        x = max([v for v in lits if v <= 10 ** 6] or [22])
        D = x.bit_length()
        steps = 4 * (2 ** D)
        bignum_bits = 400 * (2 ** D)
        note = f"Taylor + interval pow 2^{D}; {steps} Rat mults, digits grow linearly"
    elif kernel == "Math.Problems.TernaryGoldbach.HEnvFloorCert.segProp":
        # 92 segments x (1 log prec-40 + 3 exp prec-30, one with D=8)
        steps = 92 * (4 * 256 + 40)
        bignum_bits = 100000
        note = ("92 segments x (log prec 40 + 3 exp prec 30, one with D=8 => "
                "256-fold interval pow)")
    elif kernel in ("MathExtras.NumberTheory.Helfgott.AppendixACertificates.momentEval",
                    "MathExtras.NumberTheory.Helfgott.AppendixA5Certificates.numMomentEval"):
        # linear K-step midpoint/radius series, K <= 60, roundOutC 2^120
        steps = 120
        bignum_bits = 120
        note = "linear K<=60 series, roundOutC pins denominators at 2^120"
    if steps is None:
        steps = max([v for v in lits if v <= 10 ** 9] or [1])
    return kernel or "(named constants only)", shape, dom, note, steps, \
        bignum_bits, maxlit, digits


def main():
    data = json.load(open(MANIFEST))
    entries = data["native_entries"]
    os.makedirs(OUT, exist_ok=True)
    rows = []
    for e in entries:
        kernel, shape, dom, note, steps, bits, maxlit, digits = classify(e)
        rows.append({
            "axiom": e["name"],
            "family": e["family"],
            "module": e["module"],
            "origin": e["origin_declaration"],
            "primary_kernel": kernel,
            "shape_class": shape,
            "arith_domain": dom,
            "primitive_steps": steps,
            "peak_bignum_bits": bits or "",
            "max_nat_literal_digits": digits,
            "note": note,
        })
    with open(os.path.join(OUT, "native_decide_shapes.csv"), "w",
              newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)

    agg = defaultdict(lambda: {"atoms": 0, "steps": 0, "families": Counter(),
                               "modules": Counter(), "max_steps": 0})
    for r in rows:
        a = agg[(r["primary_kernel"], r["shape_class"])]
        a["atoms"] += 1
        a["steps"] += r["primitive_steps"]
        a["max_steps"] = max(a["max_steps"], r["primitive_steps"])
        a["families"][r["family"]] += 1
        a["modules"][r["module"]] += 1
    out = []
    for (k, s), a in sorted(agg.items(), key=lambda kv: -kv[1]["atoms"]):
        out.append({"primary_kernel": k, "shape_class": s,
                    "atoms": a["atoms"], "total_primitive_steps": a["steps"],
                    "max_primitive_steps": a["max_steps"],
                    "families": dict(a["families"]),
                    "modules": dict(a["modules"].most_common(6))})
    json.dump(out, open(os.path.join(OUT, "native_decide_shapes.json"), "w"),
              indent=1)

    fam = defaultdict(lambda: {"atoms": 0, "steps": 0, "shapes": Counter()})
    for r in rows:
        f = fam[r["family"]]
        f["atoms"] += 1
        f["steps"] += r["primitive_steps"]
        f["shapes"][r["shape_class"]] += 1
    famout = {k: {"atoms": v["atoms"], "total_primitive_steps": v["steps"],
                  "shapes": dict(v["shapes"])}
              for k, v in sorted(fam.items(), key=lambda kv: -kv[1]["atoms"])}
    json.dump(famout, open(os.path.join(OUT, "native_decide_families.json"),
                           "w"), indent=1)

    print(f"{len(rows)} atoms, {len(out)} distinct (kernel, shape) pairs")
    print(f"{'atoms':>6} {'total steps':>16} {'shape':<26} kernel")
    for o in out:
        print(f"{o['atoms']:>6} {o['total_primitive_steps']:>16,} "
              f"{o['shape_class']:<26} {o['primary_kernel']}")
    print()
    print(f"{'atoms':>6} {'total steps':>16}  family")
    for k, v in famout.items():
        print(f"{v['atoms']:>6} {v['total_primitive_steps']:>16,}  {k}")
    print(f"\nGRAND TOTAL primitive steps: "
          f"{sum(r['primitive_steps'] for r in rows):,}")


if __name__ == "__main__":
    main()
