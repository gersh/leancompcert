import LeanCompCert.Ports.Section413Sweep
import LeanCompCert.Ports.Section413Cells
import LeanCompCert.Ports.Section413G1TableProgram
import LeanCompCert.Ports.Section413G1TableApplications

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413Cells (encodeZ)
open LeanCompCert.Ports.Section413G1TableProgram (cellsOfWords)
open LeanCompCert.Ports.Section413G1TableApplications (hmLocalSegment)

/-! Mechanical source generator for fixed G2 endpoint tables. -/

def chunkTag (index : Nat) : String :=
  if index < 10 then s!"0{index}" else toString index

def renderChunk (start index : Nat) (words : Array (UInt64 × UInt64)) : String :=
  let tag := chunkTag index
  let rows := (List.range words.size).map fun i =>
    let p := words[i]!
    let comma := if i + 1 = words.size then "" else ","
    s!"  ({p.1.toNat}, {p.2.toNat}){comma}"
  let total := hmLocalSegment (cellsOfWords words) start words.size
  String.intercalate "\n" ([
    "import LeanCompCert.Ports.Section413G1TableApplications",
    "namespace LeanCompCert.Ports.Section413G1Generated10000Chunks",
    "open LeanCompCert.Ports.Section413Sweep",
    "open LeanCompCert.Ports.Section413G1TableProgram",
    "open LeanCompCert.Ports.Section413G1TableApplications",
    "set_option maxRecDepth 100000 in",
    "set_option maxHeartbeats 4000000 in",
    s!"def words{tag} : Array (UInt64 × UInt64) := #["] ++ rows ++ [
    "]",
    s!"def cells{tag} : Array Cell := cellsOfWords words{tag}",
    "set_option maxRecDepth 100000 in",
    "set_option maxHeartbeats 4000000 in",
    s!"theorem total{tag} : hmLocalSegment cells{tag} {start} {words.size} =",
    s!"    ({total.1}, {total.2}) := by",
    s!"  unfold cells{tag} words{tag} cellsOfWords",
    "  decide +kernel",
    "end LeanCompCert.Ports.Section413G1Generated10000Chunks",
    ""])

def renderAggregate (cap chunkLen chunkCount : Nat)
    (totals : Array (Int × Int)) : String :=
  let tags := (List.range chunkCount).map chunkTag
  let imports := tags.map fun tag =>
    s!"import LeanCompCert.Ports.Section413G1Generated10000Chunks.Chunk{tag}"
  let chunkRows := tags.map fun tag => s!"  words{tag}"
  let segmentBlocks := (List.range chunkCount).flatMap fun q =>
    let tag := chunkTag q
    let start := q * chunkLen
    let len := if start + chunkLen ≤ cap then chunkLen else cap - start
    [
      s!"theorem segment{tag} : hmTableSegment expected{cap} {start} {len} =",
      s!"    ({totals[q]!.1}, {totals[q]!.2}) := by",
      s!"  rw [hmTableSegment_eq_local expected{cap} cells{tag} {start} {len}]",
      s!"  · exact total{tag}",
      "  · intro i hi",
      s!"    change expected{cap}[{start} + i + 1]! = (cellsOfWords words{tag})[i]!",
      s!"    apply expected{cap}_lookup words{tag} ({start} + i + 1) i",
      "    · omega",
      s!"    · simpa [words{tag}] using hi",
      "    · rw [wordAt]",
      s!"      rw [show {start} + i + 1 - 1 = {start} + i by omega]",
      s!"      have hdiv : ({start} + i) / {chunkLen} = {q} := by omega",
      s!"      have hmod : ({start} + i) % {chunkLen} = i := by omega",
      "      rw [hdiv, hmod]",
      "      rfl",
      ""]
  let suffixBlocks := (List.range chunkCount).reverse.flatMap fun q =>
    let tag := chunkTag q
    let start := q * chunkLen
    let len := cap - start
    let cumulative := (List.range (chunkCount - q)).foldl (fun s j =>
      let p := totals[q + j]!
      (s.1 + p.1, s.2 + p.2)) (0, 0)
    if q + 1 = chunkCount then
      [
        s!"theorem suffix{tag} : hmTableSegment expected{cap} {start} {len} =",
        s!"    ({cumulative.1}, {cumulative.2}) := segment{tag}",
        ""]
    else
      let nextTag := chunkTag (q + 1)
      let rest := len - chunkLen
      [
        s!"theorem suffix{tag} : hmTableSegment expected{cap} {start} {len} =",
        s!"    ({cumulative.1}, {cumulative.2}) := by",
        s!"  rw [show {len} = {chunkLen} + {rest} by decide, hmTableSegment_append,",
        s!"    segment{tag}, suffix{nextTag}]",
        "  decide",
        ""]
  let total := (List.range chunkCount).foldl (fun s q =>
    let p := totals[q]!
    (s.1 + p.1, s.2 + p.2)) (0, 0)
  String.intercalate "\n" (imports ++ [
    "",
    "namespace LeanCompCert.Ports.Section413G1Generated10000Chunks",
    "open LeanCompCert.Ports.Section413Sweep",
    "open LeanCompCert.Ports.Section413Cells",
    "open LeanCompCert.Ports.Section413G1TableProgram",
    "open LeanCompCert.Ports.Section413G1TableApplications",
    "",
    s!"def chunkWords : Array (Array (UInt64 × UInt64)) := #["] ++
    (chunkRows.mapIdx fun i row =>
      let comma := if i + 1 = chunkRows.length then "" else ","
      row ++ comma) ++ [
    "]",
    "",
    s!"def wordAt (X : Nat) : UInt64 × UInt64 :=",
    s!"  if X = 0 then (0, 0) else chunkWords[(X - 1) / {chunkLen}]![(X - 1) % {chunkLen}]!",
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
    "          ({ lo := decodeZ p.1.toNat, hi := decodeZ p.2.toNat } : Cell))",
    "        C).size := by",
    "    simpa using hi",
    s!"  simp only [expected{cap}, words{cap}, cellsOfWords]",
    "  rw [getElem!_pos",
    "        (Array.map",
    "          (fun p : UInt64 × UInt64 =>",
    "            ({ lo := decodeZ p.1.toNat, hi := decodeZ p.2.toNat } : Cell))",
    s!"          (Array.map wordAt (List.range {cap + 1}).toArray))",
    "        X hleft,",
    "    getElem!_pos",
    "        (Array.map",
    "          (fun p : UInt64 × UInt64 =>",
    "            ({ lo := decodeZ p.1.toNat, hi := decodeZ p.2.toNat } : Cell))",
    "          C)",
    "        i hright,",
    "    Array.getElem_map, Array.getElem_map, List.getElem_toArray]",
    "  have hword' : wordAt X = C[i] :=",
    "    hword.trans (getElem!_pos C i hi)",
    "  simp [hword']",
    ""] ++ segmentBlocks ++ suffixBlocks ++ [
    s!"theorem total{cap} : hmTablePrefix expected{cap} {cap} =",
    s!"    ({total.1}, {total.2}) := by",
    "  rw [hmTablePrefix_eq_segment]",
    "  exact suffix00",
    "",
    s!"theorem expected{cap}_hmV1_ok : hmV1TableOK expected{cap} {cap} = true := by",
    "  unfold hmV1TableOK",
    s!"  rw [total{cap}]",
    "  decide",
    "",
    "end LeanCompCert.Ports.Section413G1Generated10000Chunks",
    ""])

def main (args : List String) : IO UInt32 := do
  if let ["chunks", capStr, lenStr, outDir] := args then
    let some cap := capStr.toNat? | do IO.eprintln "bad cap"; return 1
    let some chunkLen := lenStr.toNat? | do IO.eprintln "bad chunk length"; return 1
    if chunkLen = 0 then IO.eprintln "zero chunk length"; return 1
    IO.FS.createDirAll outDir
    let mut s : G1State := ⟨Array.replicate (cap + 1) czero, czero, true⟩
    let mut words : Array (UInt64 × UInt64) := #[]
    let mut start := 0
    let mut index := 0
    let mut totals : Array (Int × Int) := #[]
    for i in [0:cap] do
      s := g1Step 999 33 s (i + 1)
      words := words.push
        (UInt64.ofNat (encodeZ s.g.lo), UInt64.ofNat (encodeZ s.g.hi))
      if words.size = chunkLen || i + 1 = cap then
        let tag := chunkTag index
        totals := totals.push (hmLocalSegment (cellsOfWords words) start words.size)
        IO.FS.writeFile (outDir ++ s!"/Chunk{tag}.lean")
          (renderChunk start index words)
        start := start + words.size
        index := index + 1
        words := #[]
    IO.FS.writeFile (outDir ++ "/Aggregate.lean")
      (renderAggregate cap chunkLen index totals)
    IO.println s!"generated {index} chunks covering {cap} candidates"
    return 0
  if let ["chunk", capStr, startStr, lenStr, indexStr] := args then
    let some cap := capStr.toNat? | do IO.eprintln "bad cap"; return 1
    let some start := startStr.toNat? | do IO.eprintln "bad start"; return 1
    let some len := lenStr.toNat? | do IO.eprintln "bad len"; return 1
    let some index := indexStr.toNat? | do IO.eprintln "bad index"; return 1
    if start + len > cap then IO.eprintln "chunk exceeds cap"; return 1
    let mut s : G1State := ⟨Array.replicate (cap + 1) czero, czero, true⟩
    let mut words : Array (UInt64 × UInt64) := #[]
    for i in [0:start + len] do
      s := g1Step 999 33 s (i + 1)
      if start ≤ i then
        words := words.push (UInt64.ofNat (encodeZ s.g.lo), UInt64.ofNat (encodeZ s.g.hi))
    let total := hmLocalSegment (cellsOfWords words) start len
    IO.print (renderChunk start index words)
    return 0
  let [capStr] := args | do IO.eprintln "usage: CAP | chunk CAP START LEN INDEX"; return 1
  let some cap := capStr.toNat? | do IO.eprintln "bad cap"; return 1
  IO.println "import LeanCompCert.Ports.Section413Sweep"
  IO.println "import LeanCompCert.Ports.Section413Cells"
  IO.println "namespace LeanCompCert.Ports.Section413G1Generated"
  IO.println "open LeanCompCert.Ports.Section413Sweep"
  IO.println "set_option maxRecDepth 100000 in"
  IO.println "set_option maxHeartbeats 2000000 in"
  IO.println s!"def words{cap} : Array (UInt64 × UInt64) := #["
  IO.println "  (0, 0),"
  let mut s : G1State := ⟨Array.replicate (cap + 1) czero, czero, true⟩
  for i in [0:cap] do
    s := g1Step 999 1 s (i + 1)
    let comma := if i + 1 = cap then "" else ","
    IO.println s!"  ({encodeZ s.g.lo}, {encodeZ s.g.hi}){comma}"
  IO.println "]"
  IO.println "open LeanCompCert.Ports.Section413G1TableProgram"
  IO.println s!"def expected{cap} : Array Cell := cellsOfWords words{cap}"
  IO.println "end LeanCompCert.Ports.Section413G1Generated"
  return 0
