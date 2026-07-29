#!/usr/bin/env python3
"""Generate CH25-Lemma-A.7-shaped `decide` benchmarks of variable leaf count.

Reads the REAL leaf records out of claude_math's generated shards (read-only)
and re-emits a single `Chunk` of N contiguous left-edge leaves with
`theorem chunk_valid : chunk.Valid := by decide`.  This reproduces the exact
calibration shape: a `List Leaf` literal of 7-field structures with ~58-digit
`Nat` mantissas, checked by the hand-built structural `Decidable` instances.

Nothing under claude_math is written to; output goes to the scratch dir.
"""
import argparse, json, os, re, subprocess, sys, time

SRC = ("/home/gersh/claude_math/ext/ch25_certificates/CH25Certificates/"
       "LemmaA7/BoundaryStructure")
CORE = "CH25Certificates.LemmaA7.BoundaryStructureCore"
LEAN = "/home/gersh/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean"

LEAF_RE = re.compile(
    r"\{\s*edge\s*:=\s*\.(\w+)\s*,?\s*"
    r"depth\s*:=\s*(\d+)\s*,?\s*"
    r"index\s*:=\s*(\d+)\s*,?\s*"
    r"normSqUpperMantissa\s*:=\s*(\d+)\s*,?\s*"
    r"normSqUpperShift\s*:=\s*(\d+)\s*,?\s*"
    r"zetaAbsLowerMantissa\s*:=\s*(\d+)\s*,?\s*"
    r"zetaAbsLowerShift\s*:=\s*(\d+)\s*\}")


def load_leaves():
    leaves = []
    for name in sorted(os.listdir(SRC)):
        if not name.endswith(".lean"):
            continue
        text = open(os.path.join(SRC, name)).read()
        # only the `leaves` list, not the trailing `chunk` record
        body = text.split("def chunk")[0]
        for m in LEAF_RE.finditer(body):
            leaves.append({
                "edge": m.group(1), "depth": int(m.group(2)),
                "index": int(m.group(3)), "nsm": int(m.group(4)),
                "nss": int(m.group(5)), "zam": int(m.group(6)),
                "zas": int(m.group(7)),
            })
    return leaves


def contiguous_run(leaves, edge="left"):
    """Longest prefix of `edge` leaves that is gap-free on the common grid."""
    sel = [l for l in leaves if l["edge"] == edge]
    run, prev = [], None
    for l in sel:
        start = l["index"] * 2 ** (17 - l["depth"])
        if prev is None or start == prev:
            run.append(l)
            prev = (l["index"] + 1) * 2 ** (17 - l["depth"])
        else:
            break
    return run


def emit(run, n, out_dir):
    sub = run[:n]
    start = sub[0]["index"] * 2 ** (17 - sub[0]["depth"])
    finish = (sub[-1]["index"] + 1) * 2 ** (17 - sub[-1]["depth"])
    path = os.path.join(out_dir, f"Ch25Bench{n}.lean")
    with open(path, "w") as f:
        f.write(f"import {CORE}\n\n")
        f.write("set_option maxRecDepth 4000000\n")
        f.write("set_option maxHeartbeats 0\n\n")
        # mirror the generated shards exactly: the enclosing namespace, not
        # `open`, is what puts `Leaf`/`Chunk` in scope without ambiguity.
        f.write("namespace CH25Certificates.LemmaA7.BoundaryStructure.Bench\n\n")
        f.write("def leaves : List Leaf := [\n")
        parts = []
        for l in sub:
            parts.append(
                "  { edge := .%s, depth := %d, index := %d,\n"
                "    normSqUpperMantissa := %d,\n    normSqUpperShift := %d,\n"
                "    zetaAbsLowerMantissa := %d,\n    zetaAbsLowerShift := %d }"
                % (l["edge"], l["depth"], l["index"], l["nsm"], l["nss"],
                   l["zam"], l["zas"]))
        f.write(",\n".join(parts))
        f.write("]\n\n")
        f.write(f"def chunk : Chunk :=\n"
                f"  {{ edge := .{sub[0]['edge']}, startGrid := {start},\n"
                f"    finishGrid := {finish}, leafCount := {n},\n"
                f"    leaves := leaves }}\n\n")
        f.write("theorem chunk_valid : chunk.Valid := by decide\n\n")
        f.write("end CH25Certificates.LemmaA7.BoundaryStructure.Bench\n")
    return path


def run_timed(path, leanpath, timeout):
    env = dict(os.environ)
    env["LEAN_PATH"] = leanpath
    t0 = time.time()
    try:
        p = subprocess.run(["/usr/bin/time", "-v", LEAN, path],
                           capture_output=True, text=True, env=env,
                           timeout=timeout, cwd=os.path.dirname(path))
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "wall_s": timeout, "rss_kb": None,
                "cpu_s": None, "err": ""}
    err = p.stderr
    m = re.search(r"Maximum resident set size \(kbytes\): (\d+)", err)
    rss = int(m.group(1)) if m else None
    mu = re.search(r"User time \(seconds\): ([0-9.]+)", err)
    ms = re.search(r"System time \(seconds\): ([0-9.]+)", err)
    cpu = (float(mu.group(1)) + float(ms.group(1))) if (mu and ms) else None
    m = re.search(r"Elapsed \(wall clock\) time [^:]*: ([0-9:.]+)", err)
    el = None
    if m:
        el = 0.0
        for x in m.group(1).split(":"):
            el = el * 60 + float(x)
    lean_err = err.split("\tCommand being timed:")[0]
    status = "ok" if (p.returncode == 0 and "error" not in lean_err) else "fail"
    return {"status": status, "wall_s": el if el else time.time() - t0,
            "rss_kb": rss, "cpu_s": cpu, "err": lean_err[-3000:]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--leanpath", required=True)
    ap.add_argument("--sizes", default="128,256,512,1024,2048,4096,8192")
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--result", required=True)
    a = ap.parse_args()
    os.makedirs(a.out_dir, exist_ok=True)
    leaves = load_leaves()
    run = contiguous_run(leaves)
    print(f"total leaves parsed: {len(leaves)}; contiguous left run: {len(run)}",
          flush=True)
    # baseline: import only
    base = os.path.join(a.out_dir, "Ch25Base.lean")
    open(base, "w").write(f"import {CORE}\n")
    rows = [dict(run_timed(base, a.leanpath, a.timeout), n=0)]
    print(json.dumps({k: rows[0][k] for k in ("n", "status", "wall_s", "cpu_s",
                                              "rss_kb")}), flush=True)
    for n in [int(x) for x in a.sizes.split(",")]:
        if n > len(run):
            print(f"skip {n}: only {len(run)} contiguous leaves", flush=True)
            continue
        path = emit(run, n, a.out_dir)
        r = run_timed(path, a.leanpath, a.timeout)
        r["n"] = n
        r["file_bytes"] = os.path.getsize(path)
        rows.append(r)
        print(json.dumps({k: r[k] for k in ("n", "status", "wall_s", "cpu_s",
                                            "rss_kb", "file_bytes")}),
              flush=True)
        if r["status"] != "ok":
            print(r["err"][-1500:], flush=True)
            break
    json.dump(rows, open(a.result, "w"), indent=1)
    print("wrote", a.result)


if __name__ == "__main__":
    main()
