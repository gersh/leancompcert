#!/usr/bin/env python3
"""Generate + time kernel `decide +kernel` benchmarks for the leancompcert
proved-fragment pipeline, as a function of fold length.

Two routes are measured:
  route "reflect"  -- Verified.Reflect.Program with loopCount = N; the proof
                      term is O(1) and the kernel evaluates the denote fold
                      (N x |body| instruction steps).
  route "unrolled" -- Proof.foldTrace-style straight-line instruction list of
                      length ~7N; the proof term itself is O(N).
  route "chunked"  -- K certificates of C elements each, combined by a proved
                      (evaluation-free) addition lemma.

Each measurement is `/usr/bin/time -v lake env lean FILE`, so it includes the
constant elaborator/import overhead; the N=0 point measures that overhead so it
can be subtracted.
"""
import argparse, json, os, re, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GEN = os.path.join(ROOT, "bench", "gen")
RES = os.path.join(ROOT, "bench", "results")
os.makedirs(GEN, exist_ok=True)
os.makedirs(RES, exist_ok=True)

PRELUDE = """import LeanCompCert.Verified.Package
import LeanCompCert.Testing.FixedPointCertificate
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
open LeanCompCert LeanCompCert.Verified LeanCompCert.Verified.Reflect
namespace Bench
def body : List Instr := LeanCompCert.Testing.FixedPointCertificate.body
def prog (n : Nat) : Program :=
  { regCount := 20, loopCount := n, init := [], body := body,
    epilogue := [], output := 0 }
"""


def run_timed(path, timeout):
    cmd = ["/usr/bin/time", "-v", "lake", "env", "lean", path]
    t0 = time.time()
    try:
        p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "wall_s": timeout, "rss_kb": None,
                "cpu_s": None, "stdout": "", "stderr": ""}
    wall = time.time() - t0
    err = p.stderr
    m = re.search(r"Maximum resident set size \(kbytes\): (\d+)", err)
    rss = int(m.group(1)) if m else None
    mu = re.search(r"User time \(seconds\): ([0-9.]+)", err)
    ms = re.search(r"System time \(seconds\): ([0-9.]+)", err)
    cpu = (float(mu.group(1)) + float(ms.group(1))) if (mu and ms) else None
    m = re.search(r"Elapsed \(wall clock\) time [^:]*: ([0-9:.]+)", err)
    el = None
    if m:
        parts = m.group(1).split(":")
        el = 0.0
        for x in parts:
            el = el * 60 + float(x)
    # strip the time -v block from stderr for error reporting
    lean_err = err.split("\tCommand being timed:")[0]
    status = "ok" if p.returncode == 0 else "fail"
    if "error:" in lean_err or "error:" in p.stdout:
        status = "fail"
    return {"status": status, "wall_s": el if el is not None else wall,
            "rss_kb": rss, "cpu_s": cpu, "stdout": p.stdout[-4000:],
            "stderr": lean_err[-4000:]}


def eval_value(n, timeout=1800):
    path = os.path.join(GEN, f"Val{n}.lean")
    with open(path, "w") as f:
        f.write(PRELUDE)
        f.write(f"#eval (prog {n}).denote\nend Bench\n")
    p = subprocess.run(["lake", "env", "lean", path], cwd=ROOT,
                       capture_output=True, text=True, timeout=timeout)
    m = re.search(r"some (\d+)", p.stdout)
    if not m:
        raise RuntimeError(f"eval failed for n={n}: {p.stdout} {p.stderr}")
    return int(m.group(1))


def gen_reflect(n, value):
    path = os.path.join(GEN, f"Reflect{n}.lean")
    with open(path, "w") as f:
        f.write(PRELUDE)
        f.write(f"""
def expected : Nat := {value}
theorem cert : (prog {n}).denote = some expected := by decide +kernel
end Bench
""")
    return path


def gen_chunked(total, chunk, base_value, k, combine_only=False):
    """K chunks of `chunk` elements each, certified independently.

    Each chunk carries a distinct accumulator seed in its `init` block, so the
    K certificates are syntactically distinct terms and the kernel cannot share
    one chunk's evaluation with another (which would make the measurement
    meaningless).  The chunk values are then combined by a single arithmetic
    `decide +kernel` that performs no program evaluation at all -- that is the
    combining overhead."""
    path = os.path.join(GEN, f"Chunk{total}_{chunk}{'_combine' if combine_only else ''}.lean")
    seeds = [1000000 + 7919 * i for i in range(k)]
    values = [base_value + s for s in seeds]
    with open(path, "w") as f:
        f.write(PRELUDE)
        f.write(f"""
-- {k} chunks of {chunk} elements each ({total} elements total).
def seeded (seed n : Nat) : Program :=
  {{ regCount := 20, loopCount := n, init := [.binop 0 .add (.reg 0) (.lit seed)],
    body := body, epilogue := [], output := 0 }}
""")
        for i, (s, v) in enumerate(zip(seeds, values)):
            f.write(f"def v{i} : Nat := {v}\n")
            if not combine_only:
                f.write(f"theorem cert{i} : (seeded {s} {chunk}).denote = some v{i}"
                        f" := by decide +kernel\n")
        f.write("def combined : Nat := " + " + ".join(f"v{i}" for i in range(k)) + "\n")
        f.write("theorem combined_eq : combined = " + str(sum(values)) +
                " := by decide +kernel\nend Bench\n")
    return path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--route", default="reflect",
                    choices=["reflect", "chunked", "baseline"])
    ap.add_argument("--sizes", default="0,100,300,1000,3000,10000")
    ap.add_argument("--chunk", type=int, default=1000)
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    sizes = [int(x) for x in a.sizes.split(",")]
    rows = []
    for n in sizes:
        if a.route == "baseline":
            path = os.path.join(GEN, "Baseline.lean")
            with open(path, "w") as f:
                f.write(PRELUDE + "end Bench\n")
            r = run_timed(path, a.timeout)
            r.update({"route": "baseline", "n": 0})
            rows.append(r)
            break
        v = eval_value(n)
        if a.route == "reflect":
            path = gen_reflect(n, v)
            r = run_timed(path, a.timeout)
            r.update({"route": "reflect", "n": n, "value": v})
        else:
            k = max(1, n // a.chunk)
            vc = eval_value(a.chunk)
            path = gen_chunked(n, a.chunk, vc, k)
            r = run_timed(path, a.timeout)
            r.update({"route": "chunked", "n": n, "chunk": a.chunk, "k": k})
            # combining-only control: identical file with the chunk
            # certificates removed, so the difference isolates the combine cost
            cpath = gen_chunked(n, a.chunk, vc, k, combine_only=True)
            rc = run_timed(cpath, a.timeout)
            r["combine_only_wall_s"] = rc["wall_s"]
            r["combine_only_cpu_s"] = rc["cpu_s"]
            r["combine_only_rss_kb"] = rc["rss_kb"]
            r["combine_only_status"] = rc["status"]
        rows.append(r)
        print(json.dumps({kk: r[kk] for kk in
                          ("route", "n", "status", "wall_s", "cpu_s", "rss_kb")}),
              flush=True)
        if r["status"] != "ok":
            print("STOP: " + r["status"], flush=True)
            print(r["stderr"][-2000:], flush=True)
            break
    out = a.out or os.path.join(RES, f"kernel_{a.route}.json")
    with open(out, "w") as f:
        json.dump(rows, f, indent=1)
    print("wrote", out)


if __name__ == "__main__":
    main()
