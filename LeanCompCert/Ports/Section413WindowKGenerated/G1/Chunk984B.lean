import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk984A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk984B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk984A

def state06 : KState := ⟨⟨362479215948554528, 362479363662685505⟩, ⟨579550845616997820, 589370131916673400⟩, true⟩

def words05 : List Nat := [371285350097024145, 371285350010462397, 371285349935444362, 371285349939256393, 371285349908344223, 371285349864030849, 371285349818516984, 371285349764770284, 371285349603126560, 371285349546617221]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477337947821427, 362477485692798064⟩, ⟨764487335618658585, 774309659138860749⟩, true⟩

def words06 : List Nat := [371285349488183427, 371285349483738798, 371285349418089316, 371285349344350590, 371285349269228833, 371285349219311331, 371285349116441660, 371285349118127838, 371285349118748482, 371285349099512179]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493719698225505, 362493867474510193⟩, ⟨(-848704279183116436), (-838878872601226596)⟩, true⟩

def words07 : List Nat := [371285349027522786, 371285349037242362, 371285349148269498, 371285349151729400, 371285349140992829, 371285349117873805, 371285349128166962, 371285349132015110, 371285349204201518, 371285349294631829]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481043675913440, 362481191483431726⟩, ⟨399636509228215122, 409464991852940184⟩, true⟩

def words08 : List Nat := [371285349371136812, 371285349374597561, 371285349330586451, 371285349299931159, 371285349267597940, 371285349267338987, 371285349154583727, 371285349042637887, 371285348929236108, 371285348910498971]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480022690118209, 362480170528750170⟩, ⟨500250882671993588, 510082429834444962⟩, true⟩

def words09 : List Nat := [371285348931556717, 371285348996202426, 371285349059543448, 371285349063028651, 371285349055382844, 371285349070112125, 371285349125653861, 371285349129122987, 371285349079290462, 371285349030575901]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk984B
