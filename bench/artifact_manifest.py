#!/usr/bin/env python3
"""Build a run manifest for a single-artifact sweep.

    bench/artifact_manifest.py --out M.json --atom A --artifact P --family F \
        --range LO HI --emit E.txt --run cc:out.txt:time.txt [--run gcc:...]

A manifest binds, in one file: the range the sweep covers, the emitter's own
report of the configuration it built (window size, budgets, loop count, the
folded head), the toolchain (Lean, CompCert, gcc, git commit), and *every*
output slot of *every* compiler the artifact was run under -- not merely the
violation count, which on its own says nothing about whether the numbers are
the right numbers.

Exit statuses are recorded as they were observed.  `0` is agreement; for the
freestanding driver `1` is a genuine disagreement; anything else is an
abnormal termination (`128 + signal`) and is recorded as such.
"""

import argparse
import json
import re
import subprocess
import sys


def toolchain(path="runs/toolchain.txt"):
    """Read the toolchain identification captured once by

        (ccomp --version | head -1; gcc --version | head -1;
         git rev-parse HEAD; uname -srm; cat lean-toolchain) > runs/toolchain.txt

    It is read from a file rather than re-shelled here because on a box under
    heavy I/O contention a fork+exec can take minutes, and a manifest builder
    should not be the thing that hangs.
    """
    L = [x.strip() for x in open(path).read().strip().split("\n")]
    return {"compcert": L[0], "gcc": L[1], "git_commit": L[2],
            "uname": L[3], "lean": L[4]}


def parse_time(path):
    d = {}
    txt = open(path).read()
    for k, key in [("Elapsed (wall clock) time (h:mm:ss or m:ss)", "wall"),
                   ("User time (seconds)", "user_s"),
                   ("System time (seconds)", "sys_s"),
                   ("Maximum resident set size (kbytes)", "peak_rss_kb"),
                   ("Percent of CPU this job got", "cpu_pct"),
                   ("Exit status", "exit_status")]:
        m = re.search(re.escape(k) + r":\s*(\S+)", txt)
        if m:
            d[key] = m.group(1)
    if "wall" in d:
        p = [float(x) for x in d["wall"].split(":")]
        s = 0.0
        for x in p:
            s = s * 60 + x
        d["wall_s"] = round(s, 2)
    return d


def parse_run(path):
    txt = open(path).read()
    viol = re.search(r"^violations (\d+)", txt, re.M)
    slots = {int(a): int(b) for a, b in
             re.findall(r"^slot(\d+) (\d+)", txt, re.M)}
    return ({"violations": int(viol.group(1)) if viol else None,
             "slots": [slots[i] for i in sorted(slots)]}, txt)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--atom", required=True)
    ap.add_argument("--artifact", required=True)
    ap.add_argument("--family", required=True)
    ap.add_argument("--range", nargs=2, type=int, required=True)
    ap.add_argument("--emit", required=True)
    ap.add_argument("--emitcmd", default="")
    ap.add_argument("--claim", default="")
    ap.add_argument("--run", action="append", default=[],
                    help="CC:runout.txt:timefile")
    ap.add_argument("--note", default="")
    a = ap.parse_args()

    runs = {}
    outs = {}
    for spec in a.run:
        cc, outp, timep = spec.split(":")
        d, txt = parse_run(outp)
        d.update(parse_time(timep))
        runs[cc] = d
        outs[cc] = txt

    agree = None
    if len(runs) > 1:
        vals = [(r["violations"], tuple(r["slots"])) for r in runs.values()]
        agree = all(v == vals[0] for v in vals)

    m = {
        "atom": a.atom,
        "artifact": a.artifact,
        "family": a.family,
        "claim": a.claim,
        "range": a.range,
        "emit_command": a.emitcmd,
        "emit_report": open(a.emit).read().split("\tCommand being timed")[0],
        "toolchain": toolchain(),
        "runs": runs,
        "cross_compiler_agreement": agree,
        "note": a.note,
        "raw_output": outs,
    }
    with open(a.out, "w") as f:
        json.dump(m, f, indent=1)
    print(json.dumps({k: v for k, v in m.items()
                      if k not in ("raw_output", "emit_report")}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
