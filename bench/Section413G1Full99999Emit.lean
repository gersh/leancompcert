import LeanCompCert.Ports.Section413G1Full99999Certificate

/-! Emit the verified Section 4.1.3 10,000-cell table checker.

`positive` uses the proved generated table.  `control` changes the first
expected cell that the artifact actually inspects to zero, so the same machine
computation must reject it.

The check may be split into shards: `positive K N` emits an artifact whose
sweep is identical but whose epilogue inspects only shard `K` of `N`.  The
shards partition `List.range cap`, so `rawValue_zero_of_shards` recombines a
full set of passing shards into exactly the `rawValue = 0` that the unsharded
soundness chain already consumes.  Sharding therefore costs nothing in trust
and divides the emitted artifact size by roughly `N`.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413G1TableProgram
open LeanCompCert.Ports.Section413G1Generated99999Chunks
open LeanCompCert.Ports.Section413G1Full99999Certificate

/-- Start index of shard `k` of `n` in an even split of `cap` indices. -/
def shardStart (cap n k : Nat) : Nat := k * (cap / n) + min k (cap % n)

def shardLen (cap n k : Nat) : Nat :=
  cap / n + (if k < cap % n then 1 else 0)

/-- `sym` is the mangled C symbol (`ABI.mangle` already supplies the `l_`
prefix and doubles literal underscores, which a sharded name contains). -/
def driver (sym : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = " ++ sym ++ "(cells);\n" ++
  "    printf(\"flag=%llu\\n\", (unsigned long long)r);\n" ++
  "    return r == 0 ? 0 : 1;\n}\n"

def main (args : List String) : IO UInt32 := do
  let (mode, out, k, n) ←
    match args with
    | [mode, out] => pure (mode, out, 0, 1)
    | [mode, out, ks, ns] =>
        match ks.toNat?, ns.toNat? with
        | some k, some n => pure (mode, out, k, n)
        | _, _ => do IO.eprintln "shard index/count must be numerals"; return 1
    | _ => do
        IO.eprintln "usage: positive|control OUT.c [SHARD_INDEX SHARD_COUNT]"
        return 1
  if n = 0 || k ≥ n then do
    IO.eprintln s!"bad shard {k}/{n}"
    return 1
  let cap := fullCfg.cap
  let start := shardStart cap n k
  let len := shardLen cap n k
  let idxs := List.range' start len
  -- `control` must corrupt a cell this shard inspects, or it would pass.
  let some expected :=
      if mode = "positive" then some expected99999
      else if mode = "control" then some (expected99999.set! (start + 1) czero)
      else none
    | do
      IO.eprintln "mode must be positive or control"
      return 1
  let p := tableProgramOn fullCfg expected idxs
  let suffix := if n = 1 then "" else s!"_s{k}of{n}"
  let name := (if mode = "positive" then "S413G1Table99999" else
    "S413G1Table99999Control") ++ suffix
  match p.emitRolled name with
  | .error errs =>
      for e in errs do IO.eprintln e
      return 1
  | .ok src =>
      IO.FS.writeFile out (src ++ driver (LeanCompCert.ABI.mangle name) p.arrayLen)
      IO.println s!"mode={mode} shard={k}/{n} cells=[{start+1},{start+len}] \
        arrayLen={p.arrayLen} loops={p.loopCount} body={p.body.length} \
        epilogue={p.epilogue.length} out={out}"
      return 0
