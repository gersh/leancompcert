import LeanCompCert.Ports.Section413G1TableProgram
import LeanCompCert.Ports.Section413G2TableProgram

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413Cells (encodeZ)

/-! Generate bounded, table-only chunks for the 99,999-cell window sweep. -/

def chunkTag (index : Nat) : String :=
  if index < 10 then s!"00{index}"
  else if index < 100 then s!"0{index}"
  else toString index

def family (v : Nat) : String := if v = 1 then "G1" else "G2"

def indent (n : Nat) (s : String) : String :=
  String.intercalate "\n" (s.splitOn "\n" |>.map fun line => String.ofList (List.replicate n ' ') ++ line)

partial def renderWordTree (words : Array (UInt64 × UInt64)) (lo hi : Nat) : String :=
  if hi ≤ lo then "(0, 0)"
  else if hi = lo + 1 then
    let p := words[lo]!
    s!"if i = {lo} then ({p.1.toNat}, {p.2.toNat}) else (0, 0)"
  else
    let mid := (lo + hi) / 2
    s!"if i < {mid} then\n{indent 2 (renderWordTree words lo mid)}\nelse\n{indent 2 (renderWordTree words mid hi)}"

partial def renderChunkTree (tags : Array String) (lo hi : Nat) : String :=
  if hi ≤ lo then "(0, 0)"
  else if hi = lo + 1 then
    s!"if c = {lo} then wordFn{tags[lo]!} i else (0, 0)"
  else
    let mid := (lo + hi) / 2
    s!"if c < {mid} then\n{indent 2 (renderChunkTree tags lo mid)}\nelse\n{indent 2 (renderChunkTree tags mid hi)}"

def renderChunk (v index : Nat) (words : Array (UInt64 × UInt64)) : String :=
  let fam := family v
  let tag := chunkTag index
  let rows := (List.range words.size).map fun i =>
    let p := words[i]!
    let comma := if i + 1 = words.size then "" else ","
    s!"  ({p.1.toNat}, {p.2.toNat}){comma}"
  String.intercalate "\n" ([
    s!"import LeanCompCert.Ports.Section413{fam}TableProgram",
    s!"namespace LeanCompCert.Ports.Section413{fam}Generated99999Chunks",
    "open LeanCompCert.Ports.Section413Sweep",
    s!"open LeanCompCert.Ports.Section413{fam}TableProgram",
    "set_option maxRecDepth 100000 in",
    s!"def words{tag} : Array (UInt64 × UInt64) := #["] ++ rows ++ [
    "]",
    s!"def cells{tag} : Array Cell := cellsOfWords words{tag}",
    "",
    s!"def wordFn{tag} (i : Nat) : UInt64 × UInt64 :=",
    indent 2 (renderWordTree words 0 words.size),
    s!"end LeanCompCert.Ports.Section413{fam}Generated99999Chunks",
    ""])

def renderAggregate (v cap chunkLen chunkCount : Nat) : String :=
  let fam := family v
  let tags := (List.range chunkCount).map chunkTag
  let imports := tags.map fun tag =>
    s!"import LeanCompCert.Ports.Section413{fam}Generated99999Chunks.Chunk{tag}"
  let rows := tags.map fun tag => s!"  words{tag}"
  let chunkCases := tags.mapIdx fun i tag => s!"  | {i} => words{tag}"
  let chunkTree := renderChunkTree tags.toArray 0 tags.length
  String.intercalate "\n" (imports ++ [
    "",
    s!"namespace LeanCompCert.Ports.Section413{fam}Generated99999Chunks",
    "open LeanCompCert.Ports.Section413Sweep",
    "open LeanCompCert.Ports.Section413Cells",
    s!"open LeanCompCert.Ports.Section413{fam}TableProgram",
    "",
    "def chunkWords : Array (Array (UInt64 × UInt64)) := #["] ++
    (rows.mapIdx fun i row =>
      let comma := if i + 1 = rows.length then "" else ","
      row ++ comma) ++ [
    "]",
    "",
    "def chunkAt : Nat → Array (UInt64 × UInt64)"] ++ chunkCases ++ [
    "  | _ => #[]",
    "",
    "def chunkWordAt (c i : Nat) : UInt64 × UInt64 :=",
    indent 2 chunkTree,
    "",
    "def wordAt (X : Nat) : UInt64 × UInt64 :=",
    s!"  if X = 0 then (0, 0) else chunkWordAt ((X - 1) / {chunkLen}) ((X - 1) % {chunkLen})",
    "",
    s!"def words{cap} : Array (UInt64 × UInt64) :=",
    s!"  (List.range {cap + 1}).toArray.map wordAt",
    "",
    s!"def expected{cap} : Array Cell := cellsOfWords words{cap}",
    "",
    s!"theorem expected{cap}_lookup (C : Array (UInt64 × UInt64)) (X i : Nat)",
    s!"    (hX : X < {cap + 1}) (hi : i < C.size)",
    "    (hword : wordAt X = C[i]!) :",
    s!"    expected{cap}[X]! = (cellsOfWords C)[i]! := by",
    "  have hleft : X <",
    "      (Array.map",
    "        (fun p : UInt64 × UInt64 =>",
    "          ({ lo := decodeZ p.1.toNat, hi := decodeZ p.2.toNat } : Cell))",
    s!"        (Array.map wordAt (List.range {cap + 1}).toArray)).size := by",
    "    simpa using hX",
    "  have hright : i <",
    "      (Array.map",
    "        (fun p : UInt64 × UInt64 =>",
    "          ({ lo := decodeZ p.1.toNat, hi := decodeZ p.2.toNat } : Cell)) C).size := by",
    "    simpa using hi",
    s!"  simp only [expected{cap}, words{cap}, cellsOfWords]",
    "  rw [getElem!_pos",
    "        (Array.map",
    "          (fun p : UInt64 × UInt64 =>",
    "            ({ lo := decodeZ p.1.toNat, hi := decodeZ p.2.toNat } : Cell))",
    s!"          (Array.map wordAt (List.range {cap + 1}).toArray)) X hleft,",
    "    getElem!_pos",
    "        (Array.map",
    "          (fun p : UInt64 × UInt64 =>",
    "            ({ lo := decodeZ p.1.toNat, hi := decodeZ p.2.toNat } : Cell)) C) i hright,",
    "    Array.getElem_map, Array.getElem_map, List.getElem_toArray]",
    "  have hword' : wordAt X = C[i] := hword.trans (getElem!_pos C i hi)",
    "  simp [hword']",
    "",
    s!"end LeanCompCert.Ports.Section413{fam}Generated99999Chunks",
    ""])

def writeChunks (v cap chunkLen : Nat) (outDir : String) : IO UInt32 := do
  IO.FS.createDirAll outDir
  let mut index := 0
  let mut words : Array (UInt64 × UInt64) := #[]
  if v = 1 then
    let mut s : G1State := ⟨Array.replicate (cap + 1) czero, czero, true⟩
    for i in [0:cap] do
      s := g1Step 999 33 s (i + 1)
      words := words.push (UInt64.ofNat (encodeZ s.g.lo), UInt64.ofNat (encodeZ s.g.hi))
      if words.size = chunkLen || i + 1 = cap then
        let tag := chunkTag index
        IO.FS.writeFile (outDir ++ s!"/Chunk{tag}.lean") (renderChunk v index words)
        index := index + 1
        words := #[]
  else
    let mut s : G2State := ⟨Array.replicate (cap + 1) czero, czero, true⟩
    for i in [0:cap] do
      s := g2Step 999 33 s (i + 1)
      words := words.push (UInt64.ofNat (encodeZ s.g.lo), UInt64.ofNat (encodeZ s.g.hi))
      if words.size = chunkLen || i + 1 = cap then
        let tag := chunkTag index
        IO.FS.writeFile (outDir ++ s!"/Chunk{tag}.lean") (renderChunk v index words)
        index := index + 1
        words := #[]
  IO.FS.writeFile (outDir ++ "/Aggregate.lean")
    (renderAggregate v cap chunkLen index)
  IO.println s!"generated v={v} chunks={index} cells={cap}"
  return 0

def main (args : List String) : IO UInt32 := do
  let [vStr, capStr, lenStr, outDir] := args | do
    IO.eprintln "usage: V CAP CHUNKLEN OUTDIR"
    return 1
  let some v := vStr.toNat? | do IO.eprintln "bad v"; return 1
  let some cap := capStr.toNat? | do IO.eprintln "bad cap"; return 1
  let some chunkLen := lenStr.toNat? | do IO.eprintln "bad chunk length"; return 1
  if (v != 1 && v != 2) || chunkLen = 0 then
    IO.eprintln "require V=1|2 and positive chunk length"
    return 1
  writeChunks v cap chunkLen outDir
