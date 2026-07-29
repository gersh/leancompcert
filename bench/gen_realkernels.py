#!/usr/bin/env python3
"""Measure `decide +kernel` cost of claude_math's OWN certificate engines.

Rather than extrapolating from a synthetic fold, this runs the actual
functions that the 1371 `native_decide` atoms decide -- at small, tractable
parameter values -- and fits the per-step kernel cost from the measured curve.

claude_math is used strictly read-only: its compiled `.olean`s are put on
LEAN_PATH and the generated probe files live in the scratch directory.
Toolchain is claude_math's own (Lean 4.32.0), so there is no version skew in
these numbers.
"""
import argparse, json, os, re, subprocess, sys, time

LEAN = "/home/gersh/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean"

# Each probe: name -> (imports, preamble, goal-template with {n})
# The goal must be closed by `decide +kernel` and must be TRUE at every n used.
PROBES = {

  # --- RS62 anchor ladder: the 140-atom `loopE` shape (linear-fold-sieve) ---
  "rs62_loopE": {
    "imports": ["Rs62Certificates.RS62AnchorEngine"],
    "value": "(MathExtras.RS62Ladder.loopE {n} 101 0 0)",
    "type": "Nat x Nat",
  },

  # --- Chebyshev psi sweep (linear-fold-sieve, IsPrimePow + minFac) ---
  "chebyshev_psi": {
    "imports": ["AnalyticNT.Chebyshev.PsiCertEngine"],
    "value": "(AnalyticNT.ChebyshevPsi.checkAllPsiLeMul {n} 103883 100000)",
    "type": "Bool",
  },

  # --- exact-Rat transcendental enclosure: the 865-atom shape ---
  # scaled by ARGUMENT size, not by a loop count: x = 2^n
  "log_enclose": {
    "imports": ["IntervalArith.TaylorEnclosureExpLog"],
    "value": "(IntervalArith.RatInterval.log_enclose_full ((2:Rat)^{n}) 24).lo",
    "type": "Rat",
    "scale": "argument bits",
  },

  # Same kernel on a GENERIC rational: `3^n / 5` never reduces to 1 under the
  # halving loop, so the 24-term Mercator series runs on a full-width operand.
  # (The `2^n` probe above range-reduces to exactly 1, which makes the series
  # collapse -- it measures the reduction loop only.)
  "log_enclose_generic": {
    "imports": ["IntervalArith.TaylorEnclosureExpLog"],
    "value": "(IntervalArith.RatInterval.log_enclose_full ((3:Rat)^{n} / 5) 24).lo",
    "type": "Rat",
    "scale": "argument bits",
  },

  # --- Liouville/Mertens band sweep (linear-fold-sieve over mu/lambda) ---
  "cdem_rangeSweep": {
    "imports": ["TGNativeCertificates.CDEMMertensCore"],
    "value": "(TGNativeCertificates.CDEMMertens.rangeSweep {n} 1 0 true)",
    "type": "Int x Bool",
  },
}


def leanpath():
    root = "/home/gersh/claude_math"
    dirs = [f"{root}/.lake/build/lib/lean"]
    for base in ("packages",):
        d = f"{root}/.lake/{base}"
        if os.path.isdir(d):
            for p in sorted(os.listdir(d)):
                q = f"{d}/{p}/.lake/build/lib/lean"
                if os.path.isdir(q):
                    dirs.append(q)
    for base in ("ext", "forks"):
        d = f"{root}/{base}"
        if os.path.isdir(d):
            for p in sorted(os.listdir(d)):
                q = f"{d}/{p}/.lake/build/lib/lean"
                if os.path.isdir(q):
                    dirs.append(q)
    return ":".join(dirs)


def run(path, lp, timeout):
    env = dict(os.environ)
    env["LEAN_PATH"] = lp
    try:
        p = subprocess.run(["/usr/bin/time", "-v", LEAN, path],
                           capture_output=True, text=True, env=env,
                           timeout=timeout, cwd=os.path.dirname(path))
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "wall_s": timeout, "cpu_s": None,
                "rss_kb": None, "out": "", "err": ""}
    err = p.stderr
    def g(rx, cast=float):
        m = re.search(rx, err)
        return cast(m.group(1)) if m else None
    rss = g(r"Maximum resident set size \(kbytes\): (\d+)", int)
    u = g(r"User time \(seconds\): ([0-9.]+)")
    s = g(r"System time \(seconds\): ([0-9.]+)")
    m = re.search(r"Elapsed \(wall clock\) time [^:]*: ([0-9:.]+)", err)
    el = None
    if m:
        el = 0.0
        for x in m.group(1).split(":"):
            el = el * 60 + float(x)
    lean_err = err.split("\tCommand being timed:")[0]
    ok = p.returncode == 0 and "error" not in lean_err
    return {"status": "ok" if ok else "fail", "wall_s": el,
            "cpu_s": (u + s) if (u is not None and s is not None) else None,
            "rss_kb": rss, "out": p.stdout[-2000:], "err": lean_err[-2500:]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--probe", required=True, choices=list(PROBES))
    ap.add_argument("--sizes", required=True)
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--result", required=True)
    ap.add_argument("--timeout", type=int, default=1800)
    a = ap.parse_args()
    os.makedirs(a.out_dir, exist_ok=True)
    lp = leanpath()
    spec = PROBES[a.probe]
    imports = "\n".join(f"import {i}" for i in spec["imports"])
    rows = []

    # baseline: imports only
    bpath = os.path.join(a.out_dir, f"{a.probe}Base.lean")
    open(bpath, "w").write(imports + "\n")
    r = run(bpath, lp, a.timeout)
    r["n"] = 0
    rows.append(r)
    print("baseline", {k: r[k] for k in ("status", "wall_s", "cpu_s", "rss_kb")},
          flush=True)

    for n in [int(x) for x in a.sizes.split(",")]:
        # pass 1: evaluate (compiled) to learn the value
        vpath = os.path.join(a.out_dir, f"{a.probe}Val{n}.lean")
        expr = spec["value"].format(n=n)
        open(vpath, "w").write(
            imports + f"\nset_option maxRecDepth 4000000\n#eval {expr}\n")
        pv = subprocess.run([LEAN, vpath], capture_output=True, text=True,
                            env=dict(os.environ, LEAN_PATH=lp),
                            timeout=a.timeout)
        val = pv.stdout.strip().splitlines()[-1].strip() if pv.stdout.strip() else None
        if val is None or "error" in pv.stderr:
            print(f"n={n}: eval failed: {pv.stdout[-500:]} {pv.stderr[-800:]}",
                  flush=True)
            break
        # pass 2: kernel-check the equality
        cpath = os.path.join(a.out_dir, f"{a.probe}Cert{n}.lean")
        open(cpath, "w").write(
            imports + "\nset_option maxRecDepth 4000000\n"
            "set_option maxHeartbeats 0\n"
            f"theorem probe : {expr} = ({val}) := by decide +kernel\n")
        r = run(cpath, lp, a.timeout)
        r["n"] = n
        r["value"] = val[:120]
        rows.append(r)
        print(json.dumps({k: r[k] for k in
                          ("n", "status", "wall_s", "cpu_s", "rss_kb")}),
              flush=True)
        if r["status"] != "ok":
            print(r["err"][-1200:], flush=True)
            break
    json.dump(rows, open(a.result, "w"), indent=1)
    print("wrote", a.result)


if __name__ == "__main__":
    main()
