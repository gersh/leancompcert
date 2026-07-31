#!/usr/bin/env python3
"""Hardened two-phase chain driver for the `platt211` residue of
`LeanCompCert/Ports/ArraySegSieve.lean`.

    bench/platt211_chain.py --hi 1000000000000 --outdir runs/platt211

The residue tests `|Σ_{m≤n} μ(m)/m| ≤ √(2/(n+1))` (Platt's (2.11)).  The
majorant is *antitone*, so a window `[lo, hi]` is tested once, in the
epilogue, against `platt211Threshold(hi)` — the majorant at the window's
worst point — and windows must therefore be geometric.

WHY TWO PHASES, AND WHY THE EXIT CODE IS NOT THE CHECK
------------------------------------------------------
The artifact's threshold test compares the running extrema of the
accumulator, seeded with the carry-in `T(lo−1)`, against a literal.  A window
run with the *wrong* carry-in computes wrong extrema, and wrong extrema can
perfectly well stay under the threshold and report zero violations.  Zero
violations proves nothing about a link whose input was not the previous
link's output.  So:

  phase A  every window is run with the NEUTRAL carry-in (`tBias`), which is
           legitimate here and is the mode `bench/results/array_seg_folds.md`
           calls "embarrassingly parallel": the result cells hold the window's
           extrema *relative to its own carry-in*, and
           `max over [1,n] = carry-in + max relative`.  Phase A is run under
           gcc, in any order, and yields per window the triple
           `(delta, maxrel, minrel)`.

  reconcile  a serial prefix pass turns those into the true carry-in `t_i` of
           every window and the true extrema, and applies every threshold —
           the thresholds themselves being the integers the Lean emitter
           printed, not numbers this script computes.

  phase B  every window is re-emitted with its true carry-in `t_i` baked in
           as the seed literal and run under ccomp, so the ARTIFACT applies
           its own threshold test.  Phase B must report zero violations AND
           reproduce, in all three result slots, exactly what the phase-A
           reconciliation predicted, AND its carry-out must be the seed
           handed to the next window.

A one-ulp corruption of any carry-in survives the violation count and is
caught by the slot comparison; `--corrupt K` demonstrates that.

Phase A and phase B use different compilers, so agreement is also a
cross-compiler check on every window.

EXIT STATUSES
-------------
The hosted driver always returns 0.  A nonzero return from a window binary is
therefore an ABNORMAL TERMINATION (128+signal for a signal), which says
nothing about the computed value and is never reported as a disagreement.  A
genuine disagreement is a nonzero `violations` count or a slot mismatch.
"""

import argparse
import json
import math
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

M64 = 1 << 64
T_BIAS = 1 << 63          # ArraySegSieve.tBias
MOB_SCALE = 1 << 62       # ArraySegSieve.mobScale

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN_PATH = (os.path.join(ROOT, ".lake/build/lib/lean") + ":" +
             os.path.expanduser("~/.elan/toolchains/"
                                "leanprover--lean4---v4.32.1/lib/lean"))


# ---------------------------------------------------------------- schedule

def build_schedule(hi, ratio=1.02, maxseg=10 ** 6):
    """Geometric windows tiling [1, hi] exactly.

    Every window is `(lo, seglen, segcount)` with
    `hi_w = lo + seglen*segcount - 1`; consecutive windows abut and the last
    one ends at exactly `hi`.  `seglen` is a memory parameter; it is kept as
    large as the span allows (capped at `maxseg`) because the mark phase
    costs `2·π(√hi)/seglen` iterations per integer.
    """
    wins = []
    b = 0
    while b < hi:
        lo = b + 1
        u = 1
        while u * 100 <= lo and u < maxseg:
            u *= 10
        if b % u != 0:                       # re-align onto the new grid
            nb = ((b // u) + 1) * u
        else:
            nb = (int(lo * ratio) // u) * u
            if nb <= b:
                nb = b + u
        if nb > hi:
            nb = hi
        span = nb - b
        if span <= maxseg:
            seglen, segcount = span, 1
        elif span % u == 0:
            seglen, segcount = u, span // u
        else:                                # cannot happen; be loud if it does
            raise AssertionError("span %d not a multiple of u %d" % (span, u))
        assert seglen * segcount == span and seglen <= maxseg
        wins.append((lo, seglen, segcount))
        b = nb
    assert b == hi
    return wins


# ------------------------------------------------------------------- jobs

EMIT_JOB = re.compile(r"^job (\d+) lo=(\d+) hi=(\d+) thr211=(\d+)", re.M)
OUT_VIOL = re.compile(r"^violations (\d+)", re.M)
OUT_SLOT = re.compile(r"^slot(\d+) (\d+)", re.M)
EMIT_WALL = []
COMPILE_WALL = []


def platt211_threshold(hi):
    """`ArraySegSieve.platt211Threshold` in Python.

        Nat.sqrt (2^125 / N) - (N+1)/2       (Nat division throughout)

    Used to (a) cross-check every threshold the Lean emitter prints, and
    (b) supply the threshold for a window whose C the emitter produced on an
    earlier pass and which is therefore not re-emitted.  Every value it
    returns for a re-emitted window is compared against the emitter's, so a
    divergence is caught rather than trusted.
    """
    raw = math.isqrt((1 << 125) // hi)
    b = (hi + 1) // 2
    return 0 if raw <= b else raw - b


def emit_batch(jobs, workdir, tag, batches):
    """Emit every job's C in a handful of Lean processes.

    One `lean --run` per artifact pays the interpreter's start-up, which under
    memory pressure (the `.olean` page cache evicted by a 20 GB neighbour) is
    minutes rather than the half-second the emission costs.  Thousands of
    windows therefore go through `bench/ArraySegBatch.lean` instead.
    """
    env = dict(os.environ, LEAN_PATH=LEAN_PATH)
    # Emission is deterministic, so a window whose C is already on disk from an
    # earlier pass is not re-emitted: on a box whose swap is exhausted a Lean
    # start-up costs tens of minutes, and the artifact would be byte-identical.
    fresh = [j for j in jobs
             if not os.path.exists(os.path.join(workdir,
                                                "w%06d.c" % j["idx"]))]
    skipped = len(jobs) - len(fresh)
    order = sorted(fresh, key=lambda j: -j["seglen"] * j["segcount"])
    chunks = [order[i::batches] for i in range(batches)]
    files = []
    for b, ch in enumerate(chunks):
        if not ch:
            continue
        path = os.path.join(workdir, "jobs_%s_%d.txt" % (tag, b))
        with open(path, "w") as f:
            for j in ch:
                csrc = os.path.join(workdir, "w%06d.c" % j["idx"])
                line = "%d platt211 %d %d %d %s" % (
                    j["idx"], j["lo"], j["seglen"], j["segcount"], csrc)
                if j["seed"] is not None:
                    line += " %d" % j["seed"]
                f.write(line + "\n")
        files.append(path)

    def one(path):
        r = subprocess.run(["lean", "--run", "bench/ArraySegBatch.lean", path],
                           cwd=ROOT, env=env, capture_output=True, text=True)
        if r.returncode != 0:
            raise RuntimeError("batch emit rc=%d (%s): %s" %
                               (r.returncode, path, r.stderr[-3000:]))
        return r.stdout

    t0 = time.time()
    outs = []
    if files:
        with ThreadPoolExecutor(max_workers=max(1, min(len(files), 8))) as ex:
            outs = list(ex.map(one, files))
    info = {}
    for o in outs:
        for idx, lo, hi, thr in EMIT_JOB.findall(o):
            if platt211_threshold(int(hi)) != int(thr):
                raise RuntimeError(
                    "threshold divergence at window %s: emitter %s, local %d"
                    % (idx, thr, platt211_threshold(int(hi))))
            info[int(idx)] = (int(lo), int(hi), int(thr))
    for j in jobs:
        if j["idx"] not in info:
            csrc = os.path.join(workdir, "w%06d.c" % j["idx"])
            if not os.path.exists(csrc):
                raise RuntimeError("no emit record and no C for window %d"
                                   % j["idx"])
            h = j["lo"] + j["seglen"] * j["segcount"] - 1
            info[j["idx"]] = (j["lo"], h, platt211_threshold(h))
            continue
        lo, hi, _ = info[j["idx"]]
        want = j["lo"] + j["seglen"] * j["segcount"] - 1
        if lo != j["lo"] or hi != want:
            raise RuntimeError("window %d: emitter says [%d, %d], schedule "
                               "says [%d, %d]" % (j["idx"], lo, hi, j["lo"],
                                                  want))
    EMIT_WALL.append(time.time() - t0)
    print("  emitted %d artifacts in %d Lean processes (%d already on disk), "
          "%.1f s" % (len(fresh), len(files), skipped, EMIT_WALL[-1]),
          flush=True)
    return info


def compile_batch(jobs, cc, workdir, streams):
    """Compile every emitted artifact before any of them is run.

    Twelve concurrent `cc1` instances on a box whose swap is full spend their
    time in D state faulting each other's pages back in: measured medians of
    275 s and a maximum of 4617 s for a 45 kB translation unit that takes
    0.06 s on an idle machine.  A handful of sequential streams keeps one
    compiler's working set resident and turns the compile back into the
    rounding error it should be.
    """
    order = sorted(jobs, key=lambda j: j["idx"])
    chunks = [order[i::streams] for i in range(streams)]
    t0 = time.time()

    def one(chunk):
        for j in chunk:
            base = os.path.join(workdir, "w%06d" % j["idx"])
            if os.path.exists(base + ".x"):
                continue
            c = subprocess.run([cc, "-O2", "-o", base + ".x", base + ".c"],
                               capture_output=True, text=True)
            if c.returncode != 0:
                raise RuntimeError("%s rc=%d for window %d: %s"
                                   % (cc, c.returncode, j["idx"],
                                      c.stderr[-2000:]))

    with ThreadPoolExecutor(max_workers=streams) as ex:
        list(ex.map(one, [c for c in chunks if c]))
    COMPILE_WALL.append(time.time() - t0)
    print("  compiled %d artifacts with %s in %d streams, %.1f s"
          % (len(jobs), cc, streams, COMPILE_WALL[-1]), flush=True)


def run_window(idx, lo, seglen, segcount, cc, seed, workdir, hi_w, thr):
    """Run one already-emitted, already-compiled window.  Raises on abnormal
    termination."""
    base = os.path.join(workdir, "w%06d" % idx)
    csrc, exe = base + ".c", base + ".x"
    t0 = t1 = t2 = time.time()
    r = subprocess.run([exe], capture_output=True, text=True)
    t3 = time.time()
    if r.returncode != 0:
        # the hosted driver returns 0 unconditionally
        raise RuntimeError("ABNORMAL TERMINATION rc=%d (signal %s) running "
                           "window %d [%d, %d]" %
                           (r.returncode, r.returncode - 128, idx, lo, hi_w))
    mv = OUT_VIOL.search(r.stdout)
    if not mv:
        raise RuntimeError("no violation line for window %d:\n%s" %
                           (idx, r.stdout))
    slots = {int(a): int(b) for a, b in OUT_SLOT.findall(r.stdout)}
    os.unlink(csrc)
    os.unlink(exe)
    return {"idx": idx, "lo": lo, "hi": hi_w, "seglen": seglen,
            "segcount": segcount, "thr": thr, "cc": cc, "seed": seed,
            "viol": int(mv.group(1)),
            "slots": [slots[i] for i in sorted(slots)],
            "t_emit": round(t1 - t0, 3), "t_cc": round(t2 - t1, 3),
            "t_run": round(t3 - t2, 3)}


def phase(name, jobs, outdir, workers, batches, workdir, streams):
    """Run `jobs` (list of kwargs dicts) with resume from `<name>.jsonl`."""
    path = os.path.join(outdir, name + ".jsonl")
    done = {}
    if os.path.exists(path):
        with open(path) as f:
            for line in f:
                line = line.strip()
                if line:
                    d = json.loads(line)
                    done[d["idx"]] = d
    # a resumed record is only reusable if it was produced for exactly this
    # job: same range, same window shape, same compiler, same carry-in.
    for j in jobs:
        d = done.get(j["idx"])
        if d is None:
            continue
        same = (d["lo"] == j["lo"] and d["seglen"] == j["seglen"] and
                d["segcount"] == j["segcount"] and d["cc"] == j["cc"] and
                d["seed"] == j["seed"])
        if not same:
            raise RuntimeError(
                "stale record for window %d in %s: %r vs job %r -- delete the "
                "file and rerun" % (j["idx"], path, d, j))
    todo = [j for j in jobs if j["idx"] not in done]
    print("%s: %d windows, %d already done, %d to run"
          % (name, len(jobs), len(done), len(todo)), flush=True)
    if todo:
        info = emit_batch(todo, workdir, name, batches)
        compile_batch(todo, todo[0]["cc"], workdir, streams)
        # biggest first, so the tail of the run is not one huge window
        todo.sort(key=lambda j: -j["seglen"] * j["segcount"])
        lock = __import__("threading").Lock()
        fh = open(path, "a")
        n = [0]

        def work(j):
            _, hi_w, thr = info[j["idx"]]
            d = run_window(hi_w=hi_w, thr=thr, **j)
            with lock:
                fh.write(json.dumps(d) + "\n")
                fh.flush()
                done[d["idx"]] = d
                n[0] += 1
                if n[0] % 25 == 0 or n[0] == len(todo):
                    print("  %s %d/%d  last [%d, %d] %.1fs"
                          % (name, n[0], len(todo), d["lo"], d["hi"],
                             d["t_run"]), flush=True)
            return d

        with ThreadPoolExecutor(max_workers=workers) as ex:
            list(ex.map(work, todo))
        fh.close()
    return [done[j["idx"]] for j in jobs]


# ------------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--hi", type=int, default=10 ** 12)
    ap.add_argument("--ratio", type=float, default=1.02)
    ap.add_argument("--maxseg", type=int, default=10 ** 6)
    ap.add_argument("--outdir", default="runs/platt211")
    ap.add_argument("--workers", type=int, default=14)
    ap.add_argument("--phaseB-budget", type=int, default=0,
                    help="cap phase B at about this many integers "
                         "(0 = every window)")
    ap.add_argument("--streams", type=int, default=3,
                    help="concurrent compiler processes")
    ap.add_argument("--batches", type=int, default=6,
                    help="Lean processes used to emit a phase's artifacts")
    ap.add_argument("--ccA", default="gcc")
    ap.add_argument("--ccB", default="ccomp")
    ap.add_argument("--corrupt", type=int, default=-1,
                    help="perturb the phase-B carry-in of window K by 1 ulp")
    a = ap.parse_args()

    outdir = os.path.join(ROOT, a.outdir)
    work = os.path.join(outdir, "work")
    os.makedirs(work, exist_ok=True)

    wins = build_schedule(a.hi, a.ratio, a.maxseg)
    total = sum(s * c for _, s, c in wins)
    print("schedule: %d windows, %d integers, ratio %g, maxseg %d"
          % (len(wins), total, a.ratio, a.maxseg), flush=True)
    assert total == a.hi
    with open(os.path.join(outdir, "schedule.json"), "w") as f:
        json.dump({"hi": a.hi, "ratio": a.ratio, "maxseg": a.maxseg,
                   "windows": wins}, f)

    t_start = time.time()

    # ---- phase A: neutral carry-in, any order, compiler A
    jobsA = [{"idx": i, "lo": lo, "seglen": s, "segcount": c, "cc": a.ccA,
              "seed": None, "workdir": work}
             for i, (lo, s, c) in enumerate(wins)]
    resA = phase("phaseA", jobsA, outdir, a.workers, a.batches, work,
                 a.streams)

    # ---- reconcile: prefix pass over the relative extrema
    fail = []
    exempted = []
    t = T_BIAS
    seeds, predicted = [], []
    for r in resA:
        assert r["seed"] is None
        delta = (r["slots"][0] - T_BIAS) % M64
        mx = (t + (r["slots"][1] - T_BIAS)) % M64
        mn = (t + (r["slots"][2] - T_BIAS)) % M64
        seeds.append(t)
        end = (t + delta) % M64
        predicted.append((end, mx, mn))
        # An artifact's running extrema are SEEDED with T(lo-1), so a window
        # tests max/min over [lo-1, hi] -- one integer more than it covers --
        # against the majorant at hi.  At the very bottom of the range that
        # extra integer is n = 1, where the family is an exact EQUALITY
        # (S(1) = 1, sqrt(2/(1+1)) = 1), so no window whose threshold is
        # evaluated anywhere above n = 1 can carry it.  Window [1,1] tests
        # n = 1 itself and passes; window [2,2] is the one that inherits it.
        # It is exempted here, and only here, and only because it is a
        # SINGLE-INTEGER window, for which max = min = T(hi) = slot0 and the
        # endpoint test below is therefore the whole test.
        single = (r["lo"] == r["hi"])
        exempt = (r["lo"] == 2 and r["hi"] == 2 and single)
        if exempt:
            dev = min((end - T_BIAS) % M64, (T_BIAS - end) % M64)
            if dev > r["thr"]:
                fail.append(("exempt-window-endpoint", r["idx"], r["lo"],
                             r["hi"], dev, r["thr"]))
            else:
                exempted.append({"idx": r["idx"], "lo": r["lo"], "hi": r["hi"],
                                 "reason": "extrema seeded with T(1), where "
                                           "the family is an exact equality; "
                                           "single-integer window discharged "
                                           "by |T(hi)-bias| = %d <= thr = %d"
                                           % (dev, r["thr"])})
        else:
            if mx > T_BIAS + r["thr"]:
                fail.append(("reconcile-max", r["idx"], r["lo"], r["hi"], mx,
                             T_BIAS + r["thr"]))
            if mn < T_BIAS - r["thr"]:
                fail.append(("reconcile-min", r["idx"], r["lo"], r["hi"], mn,
                             T_BIAS - r["thr"]))
        t = end
    print("reconciliation: final T = %d  (= %+d ulp of 2^-62 off the bias), "
          "%d threshold failures"
          % (t, t - T_BIAS, len(fail)), flush=True)
    print("               S(%d) ~ %.12e" % (a.hi, (t - T_BIAS) / MOB_SCALE),
          flush=True)

    # ---- phase B: true carry-in, artifact applies its own test, compiler B
    #
    # Phase B recomputes the same 10^12 integers a second time.  When the
    # machine cannot afford that, `--phaseB-budget N` restricts phase B to a
    # stratified selection of windows totalling about N integers: the tightest
    # windows by |extremum|/threshold, the largest windows, and a uniform
    # sample of the rest.  Phase A's reconciliation still applies EVERY
    # threshold to EVERY window -- what a restricted phase B gives up is only
    # that the comparison was made inside the CompCert-compiled artifact
    # rather than by this script, on the windows it skips.  The manifest
    # records exactly which windows carry the artifact-side test.
    sel = list(range(len(wins)))
    if a.phaseB_budget > 0:
        spans = [w[1] * w[2] for w in wins]

        def ratio(i):
            dev = max(min((resA[i]["slots"][1] - T_BIAS) % M64,
                          (T_BIAS - resA[i]["slots"][1]) % M64),
                      min((resA[i]["slots"][2] - T_BIAS) % M64,
                          (T_BIAS - resA[i]["slots"][2]) % M64))
            return dev / max(1, resA[i]["thr"])

        chosen, used = [], 0

        def take(i, force=False):
            nonlocal used
            if i in chosen:
                return
            if not force and used + spans[i] > a.phaseB_budget:
                return
            chosen.append(i)
            used += spans[i]

        # 1. the structural extremes, unconditionally: the first window (which
        #    is where n = 1 lives), the exempted one, the last window (the one
        #    that must stop exactly at HI), and the largest window.
        for i in (0, 1, len(wins) - 1,
                  max(range(len(wins)), key=lambda j: spans[j])):
            take(i, force=True)
        # 2. the 60 tightest windows -- where a disagreement would show first.
        for i in sorted(range(len(wins)), key=lambda j: -ratio(j))[:60]:
            take(i)
        # 3. then as many windows as the budget allows, cheapest first, so the
        #    artifact-side test covers as much of the SCHEDULE as possible
        #    rather than as much of the integer line.
        for i in sorted(range(len(wins)), key=lambda j: spans[j]):
            take(i)
        sel = sorted(chosen)
        print("phase B restricted to %d of %d windows, %.4g integers "
              "(%.2f%% of the range)"
              % (len(sel), len(wins), used, 100.0 * used / a.hi), flush=True)
    selset = set(sel)

    jobsB = []
    for i, (lo, s, c) in enumerate(wins):
        if i not in selset:
            continue
        sd = seeds[i]
        if i == a.corrupt:
            sd = (sd + 1) % M64
            print("window %d: carry-in DELIBERATELY CORRUPTED (+1 ulp)" % i,
                  flush=True)
        jobsB.append({"idx": i, "lo": lo, "seglen": s, "segcount": c,
                      "cc": a.ccB, "seed": sd, "workdir": work})
    resB = phase("phaseB", jobsB, outdir, a.workers, a.batches, work,
                 a.streams)

    # ---- verify
    # the WINDOWS tile [1, hi] with no gap and no overshoot -- checked on the
    # schedule, which is what phase A swept in full
    prev_hi = 0
    for i, (lo, sg, ct) in enumerate(wins):
        if lo != prev_hi + 1:
            fail.append(("gap", i, prev_hi, lo))
        prev_hi = lo + sg * ct - 1
    if prev_hi != a.hi:
        fail.append(("endpoint", prev_hi, a.hi))

    for r in resB:
        i = r["idx"]
        want_viol = 1 if any(e["idx"] == i for e in exempted) else 0
        if r["viol"] != want_viol:
            # for the exempted window a count of 0 would mean the artifact
            # was not testing what it claims
            fail.append(("violations", i, r["lo"], r["hi"], r["viol"],
                         "wanted %d" % want_viol))
        want = predicted[i]
        got = tuple(r["slots"][:3])
        if got != want:
            fail.append(("slot-mismatch", i, r["lo"], r["hi"], got, want))
        if r["seed"] != seeds[i]:
            fail.append(("seed-mismatch", i, seeds[i], r["seed"]))
        if i + 1 < len(wins) and r["slots"][0] != seeds[i + 1]:
            fail.append(("chain-break", i, r["slots"][0], seeds[i + 1]))

    bidx = {r["idx"]: r for r in resB}
    wall = time.time() - t_start
    coreA = sum(x["t_run"] for x in resA)
    coreB = sum(x["t_run"] for x in resB)
    emit = sum(EMIT_WALL)
    comp = sum(COMPILE_WALL)

    manifest = {
        "artifact": "LeanCompCert/Ports/ArraySegSieve.lean :: mobiusProgram "
                    "with platt211Threshold",
        "atom": "residual_platt_2_11",
        "family": "PlattEq211NatFamily: |sum_{m<=n} mu(m)/m| <= sqrt(2/(n+1))",
        "range": [1, a.hi],
        "schedule": {"ratio": a.ratio, "maxseg": a.maxseg,
                     "windows": len(wins)},
        "phaseA_cc": a.ccA, "phaseB_cc": a.ccB,
        "seed_start": T_BIAS, "mobScale": MOB_SCALE,
        "final_T": t, "final_T_minus_bias": t - T_BIAS,
        "final_S_approx": (t - T_BIAS) / MOB_SCALE,
        "violations_total": sum(r["viol"] for r in resB),
        "core_seconds_phaseA_run": round(coreA, 1),
        "core_seconds_phaseB_run": round(coreB, 1),
        "emit_wall_seconds": round(emit, 1),
        "compile_wall_seconds": round(comp, 1),
        "wall_seconds": round(wall, 1),
        "exempted_windows": exempted,
        "failures": fail,
        "phaseB_windows": sorted(selset),
        "phaseB_covers_all_windows": len(selset) == len(wins),
        "windows": [{"idx": i, "lo": ra["lo"], "hi": ra["hi"],
                     "seglen": ra["seglen"], "segcount": ra["segcount"],
                     "thr": ra["thr"], "seed": seeds[i],
                     "slots": list(predicted[i]),
                     "viol": bidx[i]["viol"] if i in bidx else None,
                     "artifact_side_test": i in bidx,
                     "relA": ra["slots"][:3],
                     "t_run_A": ra["t_run"],
                     "t_run_B": bidx[i]["t_run"] if i in bidx else None}
                    for i, ra in enumerate(resA)],
    }
    mpath = os.path.join(outdir, "manifest.json")
    with open(mpath, "w") as f:
        json.dump(manifest, f, indent=1)

    if fail:
        print("CHAIN REJECTED, %d failures:" % len(fail))
        for x in fail[:40]:
            print("  ", x)
        print("manifest:", mpath)
        return 1
    for e in exempted:
        print("EXEMPTED window %d [%d, %d]: %s" % (e["idx"], e["lo"], e["hi"],
                                                   e["reason"]))
    print("chain accepted: [1, %d], %d windows, every phase-B "
          "slot reproduces the phase-A reconciliation, carry-outs chain, "
          "endpoint exact, %d exempted window(s)."
          % (a.hi, len(wins), len(exempted)))
    print("manifest:", mpath)
    return 0


if __name__ == "__main__":
    sys.exit(main())
