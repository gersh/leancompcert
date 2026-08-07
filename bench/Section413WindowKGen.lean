import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

/-! Reproduce the bounded proof shards for both 99,999-step Section 4.13 K traces. -/

def renderInt (z : Int) : String := if z < 0 then s!"({z})" else toString z
def renderCell (c : Cell) : String := s!"⟨{renderInt c.lo}, {renderInt c.hi}⟩"
def renderState (s : KState) : String := s!"⟨{renderCell s.k1}, {renderCell s.k2}, {s.ok}⟩"
def renderWords (xs : List Nat) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"
def pad3 (n : Nat) : String :=
  let s := toString n
  String.join (List.replicate (3 - s.length) "0") ++ s
def pad2 (n : Nat) : String :=
  let s := toString n
  String.join (List.replicate (2 - s.length) "0") ++ s
def indent (n : Nat) (s : String) : String :=
  String.intercalate "\n" (s.splitOn "\n" |>.map fun line => String.ofList (List.replicate n ' ') ++ line)

partial def renderChunkTree (lo hi : Nat) : String :=
  if hi ≤ lo then "[]"
  else if hi = lo + 1 then
    s!"if c = {lo} then Chunk{pad3 lo}.words else []"
  else
    let mid := (lo + hi) / 2
    s!"if c < {mid} then\n{indent 2 (renderChunkTree lo mid)}\nelse\n{indent 2 (renderChunkTree mid hi)}"

def emitKind (dir kind gname : String) (G : Nat → Cell)
    (v lo : Nat) (boundNum : Int) (offset : Nat) : IO Unit := do
  let mut p := initialKState
  let mut imports : List String := []
  for i in List.range 1000 do
    let tag := pad3 i
    let ns := s!"LeanCompCert.Ports.Section413WindowKGenerated.{kind}.Chunk{tag}"
    imports := imports ++ [s!"import {ns}"]
    let segStart := i * 100
    let segLen := min 100 (99999 - segStart)
    let mut body :=
      "import LeanCompCert.Ports.Section413WindowRuntime\n" ++
      "import LeanCompCert.Ports.Section413WindowDirectTables\n\n" ++
      s!"namespace {ns}\n\n" ++
      "open LeanCompCert.Ports.Section413Sweep\n" ++
      "open LeanCompCert.Ports.Section413WindowRuntime\n" ++
      "open LeanCompCert.Ports.Section413WindowDirectTables\n\n" ++
      s!"def state00 : KState := {renderState p}\n\n"
    let mut wordNames : List String := []
    let mut done := 0
    for j in List.range 10 do
      if done < segLen then
        let microLen := min 10 (segLen - done)
        let microStart := segStart + done
        let result := trace G v lo boundNum offset microStart microLen p
        let jtag := pad2 j
        let nextTag := pad2 (j + 1)
        let wordName := s!"words{jtag}"
        wordNames := wordNames ++ [wordName]
        body := body ++
          s!"def state{nextTag} : KState := {renderState result.1}\n\n" ++
          s!"def {wordName} : List Nat := {renderWords result.2}\n\n" ++
          "set_option maxRecDepth 100000 in\n" ++
          s!"theorem micro{jtag} :\n" ++
          s!"    trace {gname} {v} {lo} {boundNum} {offset} {microStart} {microLen} state{jtag} =\n" ++
          s!"      (state{nextTag}, {wordName}) := by\n  decide +kernel\n\n"
        if j = 0 then
          body := body ++ s!"theorem prefix{nextTag} :\n" ++
            s!"    trace {gname} {v} {lo} {boundNum} {offset} {segStart} {microLen} state00 =\n" ++
            s!"      (state{nextTag}, {wordName}) := micro{jtag}\n\n"
        else
          let allWords := String.intercalate " ++ " wordNames
          body := body ++ s!"theorem prefix{nextTag} :\n" ++
            s!"    trace {gname} {v} {lo} {boundNum} {offset} {segStart} {done + microLen} state00 =\n" ++
            s!"      (state{nextTag}, {allWords}) := by\n" ++
            s!"  rw [show {done + microLen} = {done} + {microLen} by decide, trace_append, prefix{jtag}]\n" ++
            s!"  simp only [Nat.reduceAdd]\n  rw [micro{jtag}]\n\n"
        p := result.1
        done := done + microLen
    let wordsExpr := String.intercalate " ++ " wordNames
    let finalStateTag := pad2 wordNames.length
    body := body ++ s!"def words : List Nat := {wordsExpr}\n\n" ++
      s!"theorem segment :\n" ++
      s!"    trace {gname} {v} {lo} {boundNum} {offset} {segStart} {segLen} state00 =\n" ++
      s!"      (state{finalStateTag}, words) := by\n" ++
      s!"  simpa only [words] using prefix{finalStateTag}\n\n" ++
      s!"end {ns}\n"
    IO.FS.writeFile s!"{dir}/{kind}/Chunk{tag}.lean" body
    if i % 100 = 99 then IO.println s!"{kind}: emitted {i + 1}/1000"

  let mut prefixProofs := ""
  for i in List.range 1000 do
    let k := i + 1
    let total := min 99999 (k * 100)
    let prev := i * 100
    let len := total - prev
    let tag := pad3 i
    if i = 0 then
      prefixProofs := prefixProofs ++ "\ntheorem prefix001 :\n" ++
        s!"    trace {gname} {v} {lo} {boundNum} {offset} 0 {total} initialKState =\n" ++
        s!"      (Chunk{tag}.state10, prefixWords 1) := by\n" ++
        s!"  simpa [prefixWords, chunk, Chunk{tag}.state00, initialKState, czero] using\n" ++
        s!"    Chunk{tag}.segment\n"
    else
      let prevTag := pad3 (i - 1)
      prefixProofs := prefixProofs ++ s!"\ntheorem prefix{pad3 k} :\n" ++
        s!"    trace {gname} {v} {lo} {boundNum} {offset} 0 {total} initialKState =\n" ++
        s!"      (Chunk{tag}.state10, prefixWords {k}) := by\n" ++
        s!"  rw [show {total} = {prev} + {len} by decide, trace_append,\n" ++
        s!"    prefix{pad3 i}, show Chunk{prevTag}.state10 = Chunk{tag}.state00 by rfl]\n" ++
        "  simp only [Nat.zero_add]\n" ++
        s!"  rw [Chunk{tag}.segment]\n  rfl\n"
  let aggregate := String.intercalate "\n" imports ++ "\n\n" ++
    "set_option maxRecDepth 100000\n\n" ++
    s!"namespace LeanCompCert.Ports.Section413WindowKGenerated.{kind}\n\n" ++
    "open LeanCompCert.Ports.Section413Sweep\n" ++
    "open LeanCompCert.Ports.Section413WindowRuntime\n" ++
    "open LeanCompCert.Ports.Section413WindowDirectTables\n\n" ++
    "def chunk (c : Nat) : List Nat :=\n" ++ indent 2 (renderChunkTree 0 1000) ++ "\n\n" ++
    "def prefixWords : Nat → List Nat\n  | 0 => []\n" ++
    "  | n + 1 => prefixWords n ++ chunk n\n" ++ prefixProofs ++ "\n\n" ++
    "def allWords : List Nat := prefixWords 1000\n\n" ++
    s!"theorem fullTrace :\n    trace {gname} {v} {lo} {boundNum} {offset} 0 99999 initialKState =\n" ++
    "      (Chunk999.state10, allWords) := by\n  exact prefix1000\n\n" ++
    s!"end LeanCompCert.Ports.Section413WindowKGenerated.{kind}\n"
  IO.FS.writeFile s!"{dir}/{kind}/Aggregate.lean" aggregate

def main (args : List String) : IO UInt32 := do
  let [outDir] := args | do
    IO.eprintln "usage: OUTDIR"
    return 1
  IO.FS.createDirAll s!"{outDir}/G1"
  IO.FS.createDirAll s!"{outDir}/G2"
  emitKind outDir "G1" "directG1" directG1 1 40 36393 (880 * unitScale)
  emitKind outDir "G2" "directG2" directG2 2 16 37273 0
  return 0
