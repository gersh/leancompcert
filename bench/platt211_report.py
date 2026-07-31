#!/usr/bin/env python3
"""Summarise a `bench/platt211_chain.py` manifest into the numbers a results
document wants: cost, rate, the worst window, and the checks that were run.

    bench/platt211_report.py runs/platt211/manifest.json [--refseg FILE]

`--refseg` is the output of `bench/ref_seg.c` run from 1 to some window
boundary; its `slot0` is an independent computation of the same accumulator
and must equal the chain's carry-out at that boundary.
"""

import argparse
import json
import re
import sys

M64 = 1 << 64
T_BIAS = 1 << 63
MOB_SCALE = 1 << 62


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("manifest")
    ap.add_argument("--refseg", default=None)
    a = ap.parse_args()
    m = json.load(open(a.manifest))
    w = m["windows"]

    tot = sum(x["hi"] - x["lo"] + 1 for x in w)
    tA = sum(x["t_run_A"] for x in w)
    tB = sum(x["t_run_B"] for x in w if x["t_run_B"] is not None)
    totB = sum(x["hi"] - x["lo"] + 1 for x in w
               if x.get("artifact_side_test"))

    # The artifact's literal is platt211Threshold(hi) = floor(2^62*sqrt(2/hi))
    # - ceil(hi/2), i.e. the majorant at `hi`.  The Nat family the axiom
    # reduces to wants the majorant at `hi+1`, because on the real cell
    # [n, n+1) the antitone sqrt(2/x) bottoms out at x -> n+1.  For hi below
    # about 3.4e7 the difference, 2^62*sqrt2*(1/sqrt(hi) - 1/sqrt(hi+1)) ~
    # 3.26e18/hi^1.5, exceeds the ceil(hi/2) the artifact already subtracts,
    # so for those windows the artifact's own literal does NOT by itself carry
    # the (n+1) form.  It is recovered here, exactly, from the same result
    # cells: every window is re-tested against the STRICTER integer
    # floor(2^62*sqrt(2/(hi+1))) - ceil(hi/2).
    import math
    strict_fail = []
    worst_strict = None
    for x in w:
        hi = x["hi"]
        thr_s = math.isqrt((1 << 125) // (hi + 1)) - (hi + 1) // 2
        if thr_s < 0:
            thr_s = 0
        dev = max(min((x["slots"][1] - T_BIAS) % M64,
                      (T_BIAS - x["slots"][1]) % M64),
                  min((x["slots"][2] - T_BIAS) % M64,
                      (T_BIAS - x["slots"][2]) % M64))
        if x["lo"] == 2 and x["hi"] == 2:
            dev = min((x["slots"][0] - T_BIAS) % M64,
                      (T_BIAS - x["slots"][0]) % M64)
        if dev > thr_s:
            strict_fail.append((x["idx"], x["lo"], hi, dev, thr_s))
        r = dev / thr_s if thr_s else float("inf")
        if x["lo"] <= 2:
            continue          # the n = 1 exact tie; reported separately
        if worst_strict is None or r > worst_strict[0]:
            worst_strict = (r, x["idx"], x["lo"], hi, dev, thr_s)

    # tightness: |extremum - bias| against the window's own threshold
    worst = None
    for x in w:
        dev = max(min((x["slots"][1] - T_BIAS) % M64,
                      (T_BIAS - x["slots"][1]) % M64),
                  min((x["slots"][2] - T_BIAS) % M64,
                      (T_BIAS - x["slots"][2]) % M64))
        r = dev / x["thr"]
        if x["lo"] <= 2:
            continue          # the n = 1 exact tie; reported separately
        if worst is None or r > worst[0]:
            worst = (r, x["idx"], x["lo"], x["hi"], dev, x["thr"])

    print("range              [%d, %d]" % tuple(m["range"]))
    print("windows            %d, ratio %g, maxseg %d"
          % (m["schedule"]["windows"], m["schedule"]["ratio"],
             m["schedule"]["maxseg"]))
    print("integers covered   %d" % tot)
    print("phase A (%-5s)    %.1f core-s = %.2f core-h, %.1f ns/integer"
          % (m["phaseA_cc"], tA, tA / 3600, tA * 1e9 / tot))
    print("phase B (%-5s)    %.1f core-s = %.2f core-h, %.1f ns/integer, "
          "%d of %d windows (%.2f%% of the integers)"
          % (m["phaseB_cc"], tB, tB / 3600,
             (tB * 1e9 / totB) if totB else 0,
             len(m.get("phaseB_windows", [])), len(w),
             100.0 * totB / tot))
    print("emission           %.1f s wall (batched)"
          % m.get("emit_wall_seconds", 0))
    print("compile            %.1f s wall (batched)" % m.get("compile_wall_seconds", 0))
    print("wall               %.1f s = %.2f h"
          % (m["wall_seconds"], m["wall_seconds"] / 3600))
    print("violations total   %d" % m["violations_total"])
    print("exempted windows   %s"
          % ([e["idx"] for e in m.get("exempted_windows", [])]))
    print("failures           %s" % (m["failures"] or "none"))
    print("final T            %d" % m["final_T"])
    print("S(hi)              %.15e" % m["final_S_approx"])
    print("worst window (n>2) ratio %.4f at #%d [%d, %d]: |dev| %d vs thr %d"
          % worst)
    print("strict (hi+1) form failures: %s"
          % (strict_fail if strict_fail else "none -- every window also "
             "clears floor(2^62*sqrt(2/(hi+1))) - ceil(hi/2)"))
    print("worst strict (n>2) ratio %.4f at #%d [%d, %d]: |dev| %d vs thr %d"
          % worst_strict)

    if a.refseg:
        txt = open(a.refseg).read()
        mm = (re.search(r"^mobius\s+slot0 (\d+)", txt, re.M) or
              re.search(r"^slot0 (\d+)", txt, re.M))
        s0 = int(mm.group(1))
        # find the window whose hi is the boundary ref_seg stopped at
        hit = None
        for i, x in enumerate(w):
            if x["slots"][0] == s0:
                hit = x
        print("ref_seg slot0      %d" % s0)
        if hit:
            print("  MATCHES the chain's carry-out at window #%d, [%d, %d] "
                  "-- an independent segmented sieve, sharing no code with "
                  "the artifact, reproduces the accumulator at n = %d"
                  % (hit["idx"], hit["lo"], hit["hi"], hit["hi"]))
        else:
            print("  NO MATCH against any window carry-out -- investigate")
    return 0


if __name__ == "__main__":
    sys.exit(main())
