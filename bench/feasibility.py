#!/usr/bin/env python3
"""Per-family feasibility extrapolation for moving claude_math's 1371
`native_decide` atoms to kernel-checked proofs.

Combines
  * bench/results/native_decide_shapes.csv  (per-atom shape + exact scale)
  * the measured cost laws in bench/results/real_*.json, ch25_scaling.json
    and kernel_reflect_cpu.json

and emits, per family, the predicted single-core CPU time, the number of
kernel `decide`s needed under an 8 GB per-`decide` memory budget, and a
verdict.  Every cost coefficient is a fit to a measured sweep; `--show-laws`
prints the fits and their provenance.
"""
import csv, json, math, os, sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "results")

BUDGET_RSS_MB = 8000.0     # per `decide`: keeps 10-way parallelism inside 80 GB
CORES = 20


def load(name):
    p = os.path.join(RES, name)
    return json.load(open(p)) if os.path.exists(p) else None


def marginal(rows, key):
    base = next((r for r in rows if r.get("n") == 0), None)
    b = (base.get(key) or 0.0) if base else 0.0
    return [(r["n"], (r.get(key) or 0.0) - b)
            for r in rows if r.get("n") and r.get("status") == "ok"
            and r.get(key) is not None]


def fit_power_offset(points, floor, min_n=0.0):
    """Fit t = floor + a*n^b, i.e. a power law above a fixed per-call floor.

    Used where the measurement has a constant start-up cost (one
    `log_enclose_full` call pays a fixed reduction cost before the series runs).
    `min_n` drops the floor-dominated small end, where the residual is noise and
    fitting it flattens the exponent and under-predicts the large arguments that
    actually cost something."""
    pts = [(n, t - floor) for n, t in points if n >= min_n and t > floor]
    return fit_power(pts)


def fit_power(points):
    pts = [(n, t) for n, t in points if n > 0 and t > 0]
    if len(pts) < 2:
        return None
    lx = [math.log(n) for n, _ in pts]
    ly = [math.log(t) for _, t in pts]
    k = len(pts)
    mx, my = sum(lx) / k, sum(ly) / k
    b = (sum((x - mx) * (y - my) for x, y in zip(lx, ly))
         / sum((x - mx) ** 2 for x in lx))
    return math.exp(my - b * mx), b


LAWS = {}


def add(name, rows, unit, basis, xform=lambda n: n):
    if not rows:
        return
    c = [(xform(n), v) for n, v in marginal(rows, "cpu_s")]
    s = [(xform(n), v / 1024.0) for n, v in marginal(rows, "rss_kb")]
    floor = 0.0
    if name == "log_enclose_full":
        floor = 0.08          # measured fixed cost of one call (see report 2.4)
    fc = fit_power_offset(c, floor, min_n=30.0) if floor else fit_power(c)
    fs = fit_power(s)
    if fc and fs:
        LAWS[name] = {"cpu": fc, "rss": fs, "unit": unit, "basis": basis,
                      "floor": floor, "n_points": len(c),
                      "range": (min(n for n, _ in c), max(n for n, _ in c))}


def build_laws():
    add("log_enclose_full", load("real_log.json"), "argument decimal digits",
        "gen_realkernels.py --probe log_enclose (IntervalArith, Lean 4.32.0)",
        xform=lambda n: n * math.log10(2))
    add("rs62_loopE", load("real_rs62.json"), "iterations",
        "gen_realkernels.py --probe rs62_loopE (MathExtras.RS62Ladder.loopE)")
    add("chebyshev_psi", load("real_psi.json"), "iterations",
        "gen_realkernels.py --probe chebyshev_psi "
        "(AnalyticNT.ChebyshevPsi.checkAllPsiLeMul)")
    add("cdem_rangeSweep", load("real_cdem.json"), "iterations",
        "gen_realkernels.py --probe cdem_rangeSweep "
        "(TGNativeCertificates.CDEMMertens.rangeSweep)")
    add("ch25_leaf", load("ch25_scaling.json"), "leaves",
        "gen_ch25.py on the real CH25 Lemma A.7 leaf records")
    r = load("kernel_reflect_cpu.json")
    if r:
        rows = [dict(x, n=x["n"]) for x in r]
        rows.append({"n": 0, "cpu_s": 0.165, "rss_kb": 437848, "status": "ok"})
        add("leancompcert_reflect", rows, "fold elements",
            "gen_kernel.py --route reflect (leancompcert CCIR, Lean 4.32.1)")


# Which measured law prices which atom.  Engine-specific first, then a
# same-shape proxy.  `exact` = the atom's own engine was measured.
def law_for(kernel, shape):
    if "RS62Ladder" in kernel or "RS62MertensFirst" in kernel:
        return "rs62_loopE", "exact"
    if "ChebyshevPsi" in kernel:
        return "chebyshev_psi", "exact"
    if "CDEMMertens" in kernel:
        return "cdem_rangeSweep", "exact"
    if "log_enclose_full" in kernel:
        return "log_enclose_full", "exact"
    if shape == "transcendental-enclosure":
        return "log_enclose_full", "proxy: same exact-Rat series engine"
    if shape == "bisection-tree":
        return "log_enclose_full", ("proxy: each cell priced as its "
                                    "transcendental nodes")
    if shape == "linear-fold-sieve":
        return "rs62_loopE", ("proxy: same per-step work (one minFac / "
                              "IsPrimePow / Squarefree decision)")
    if shape == "linear-fold-nat":
        return "cdem_rangeSweep", "proxy: cheapest measured fold engine"
    if shape == "linear-fold-rat":
        return "chebyshev_psi", ("proxy, LOWER BOUND: exact-Rat folds also "
                                 "suffer denominator growth")
    if shape == "table-streaming":
        return None, "no kernel route: needs an Array Nat of length >= 1.5e6"
    return "CONSTANT", "constant depth, below measurement resolution"


def price(law, scale):
    L = LAWS[law]
    ca, cb = L["cpu"]
    ra, rb = L["rss"]
    cpu = L.get("floor", 0.0) + ca * scale ** cb
    rss = ra * scale ** rb
    if rss <= BUDGET_RSS_MB:
        return cpu, rss, 1
    # chunk: solve rss(nchunk) = budget, then k chunks of that size
    nchunk = max(1.0, (BUDGET_RSS_MB / ra) ** (1.0 / rb))
    k = math.ceil(scale / nchunk)
    return k * ca * nchunk ** cb, BUDGET_RSS_MB, k


def fmt(s):
    if s is None:
        return "n/a"
    if s < 90:
        return f"{s:.0f} s"
    if s < 5400:
        return f"{s/60:.0f} min"
    if s < 86400 * 2:
        return f"{s/3600:.1f} h"
    if s < 86400 * 730:
        return f"{s/86400:.1f} d"
    return f"{s/86400/365:.1f} y"


def main():
    build_laws()
    rows = list(csv.DictReader(open(os.path.join(
        RES, "native_decide_shapes.csv"))))

    print("=== measured kernel cost laws (fits to this session's sweeps) ===")
    for k, v in LAWS.items():
        ca, cb = v["cpu"]; ra, rb = v["rss"]
        print(f"{k}")
        print(f"   cpu_s   = {ca:.4g} * n^{cb:.3f}     [n = {v['unit']}, "
              f"{v['n_points']} points over {v['range'][0]:.0f}-{v['range'][1]:.0f}]")
        print(f"   rss_MB  = {ra:.4g} * n^{rb:.3f}")
        print(f"   basis   : {v['basis']}")
    print()

    out = []
    for r in rows:
        kernel, shape = r["primary_kernel"], r["shape_class"]
        law, why = law_for(kernel, shape)
        if shape == "transcendental-enclosure" or (
                law == "log_enclose_full" and shape == "bisection-tree"):
            # priced by operand width; bisection trees pay it per cell
            digits = max(3, int(r["max_nat_literal_digits"] or 3))
            cells = 1
            if shape == "bisection-tree":
                cells = max(1, int(r["primitive_steps"]) // 30)
            if law:
                c1, m1, _ = price(law, digits)
                cpu = c1 * cells
                # memory accumulates across the cells of one `decide`; if the
                # whole tree busts the budget the range is split, exactly as a
                # fold would be chunked
                total_rss = m1 * cells
                k = max(1, math.ceil(total_rss / BUDGET_RSS_MB))
                rss = min(total_rss, BUDGET_RSS_MB)
            else:
                cpu = rss = k = None
        elif law == "CONSTANT":
            # constant-depth arithmetic on named repository constants: below
            # the resolution of every sweep here (< 0.1 s, < 10 MB)
            cpu, rss, k = 0.1, 10.0, 1
        elif law is None:
            cpu = rss = k = None
        else:
            cpu, rss, k = price(law, max(1, int(r["primitive_steps"])))
        out.append(dict(r, law=law or "", law_note=why,
                        pred_cpu_s=cpu, pred_rss_mb=rss, decides=k))

    fam = defaultdict(lambda: dict(atoms=0, cpu=0.0, rss=0.0, decides=0,
                                   nokernel=0, steps=0, exact=0,
                                   shapes=defaultdict(int)))
    for r in out:
        f = fam[r["family"]]
        f["atoms"] += 1
        f["steps"] += int(r["primitive_steps"])
        f["shapes"][r["shape_class"]] += 1
        if r["law_note"] == "exact":
            f["exact"] = f.get("exact", 0) + 1
        if r["pred_cpu_s"] is None:
            f["nokernel"] += 1
        else:
            f["cpu"] += r["pred_cpu_s"]
            f["rss"] = max(f["rss"], r["pred_rss_mb"])
            f["decides"] += r["decides"]

    def verdict(v):
        if v["nokernel"] == v["atoms"]:
            return "INFEASIBLE (no kernel route)"
        if v["nokernel"]:
            return f"PARTIAL ({v['nokernel']} atoms infeasible)"
        if v["cpu"] > 86400 * 365:
            return "INFEASIBLE (> 1 core-year)"
        if v["cpu"] > 86400 * 7:
            return "CHUNK + CLUSTER"
        if v["decides"] > v["atoms"]:
            return "NEEDS CHUNKING"
        return "FEASIBLE NOW"

    hdr = (f"{'atoms':>5} {'exact':>6} {'decides':>8} {'CPU (1 core)':>13} "
           f"{'wall @20':>9} {'RSS/dec':>9}  {'verdict':<28} family")
    print(hdr); print("-" * len(hdr))
    T = dict(atoms=0, cpu=0.0, decides=0, nokernel=0)
    for k, v in sorted(fam.items(), key=lambda kv: -kv[1]["cpu"]):
        T["atoms"] += v["atoms"]; T["cpu"] += v["cpu"]
        T["decides"] += v["decides"]; T["nokernel"] += v["nokernel"]
        print(f"{v['atoms']:>5} {v['exact']:>6} {v['decides']:>8} {fmt(v['cpu']):>13} "
              f"{fmt(v['cpu']/CORES):>9} {v['rss']:>6.0f} MB  "
              f"{verdict(v):<28} {k}")
    print("-" * len(hdr))
    print(f"{T['atoms']:>5} {'':>6} {T['decides']:>8} {fmt(T['cpu']):>13} "
          f"{fmt(T['cpu']/CORES):>9} {'':>9}  "
          f"{T['nokernel']} atoms with no kernel route")

    json.dump({k: {"atoms": v["atoms"], "primitive_steps": v["steps"],
                   "pred_cpu_s": v["cpu"],
                   "pred_wall_s_at_20_cores": v["cpu"] / CORES,
                   "kernel_decides": v["decides"],
                   "peak_rss_mb_per_decide": v["rss"],
                   "atoms_with_no_kernel_route": v["nokernel"],
                   "verdict": verdict(v), "shapes": dict(v["shapes"]),
                   "atoms_priced_by_their_own_measured_engine": v["exact"]}
               for k, v in fam.items()},
              open(os.path.join(RES, "feasibility_by_family.json"), "w"),
              indent=1)
    with open(os.path.join(RES, "feasibility_by_atom.csv"), "w",
              newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(out[0]))
        w.writeheader(); w.writerows(out)

    # by shape as well
    sh = defaultdict(lambda: dict(atoms=0, cpu=0.0, decides=0, nokernel=0))
    for r in out:
        s = sh[r["shape_class"]]
        s["atoms"] += 1
        if r["pred_cpu_s"] is None:
            s["nokernel"] += 1
        else:
            s["cpu"] += r["pred_cpu_s"]; s["decides"] += r["decides"]
    print("\nby shape:")
    for k, v in sorted(sh.items(), key=lambda kv: -kv[1]["cpu"]):
        print(f"  {v['atoms']:>5} atoms {v['decides']:>8} decides "
              f"{fmt(v['cpu']):>12}  {k}"
              + (f"   ({v['nokernel']} with no route)" if v["nokernel"] else ""))
    json.dump({k: dict(v) for k, v in sh.items()},
              open(os.path.join(RES, "feasibility_by_shape.json"), "w"),
              indent=1)
    print("\nwrote feasibility_by_family.json / feasibility_by_shape.json / "
          "feasibility_by_atom.csv")


if __name__ == "__main__":
    main()
