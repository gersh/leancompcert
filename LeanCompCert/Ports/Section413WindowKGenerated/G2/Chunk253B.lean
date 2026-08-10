import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk253A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk253B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk253A

def state06 : KState := ⟨⟨360522810388204631, 360522814200466620⟩, ⟨1539268581854346916, 1539333982824646468⟩, true⟩

def words05 : List Nat := [360583525581603134, 360583525172550027, 360583524763496152, 360583523550556255, 360583522387268837, 360583520203546311, 360583518019899384, 360583517387770387, 360583515883266672, 360583513490010179]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 25350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 25300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593779147169021, 360593782962566810⟩, ⟨(-261028080854107030), (-260962600344459818)⟩, true⟩

def words06 : List Nat := [360583511096872386, 360583508661990059, 360583507035528601, 360583505850714767, 360583504665968396, 360583502171900155, 360583499461329107, 360583498301053778, 360583497140767392, 360583497100742505]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 25360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 25300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360555094069331402, 360555097887889504⟩, ⟨720712855120087730, 720778415822398290⟩, true⟩

def words07 : List Nat := [360583497101040859, 360583496732908446, 360583497545587105, 360583499503541151, 360583500220935455, 360583500938323425, 360583500938621074, 360583500477769093, 360583498471290416, 360583497352657921]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 25370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 25300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573496520617917, 360573500342306313⟩, ⟨253610047908464456, 253675688073383686⟩, true⟩

def words08 : List Nat := [360583496234001062, 360583495623187611, 360583495415333395, 360583494425749707, 360583493436189387, 360583492050979143, 360583491872842091, 360583492304650398, 360583492304955653, 360583491507649889]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 25380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 25300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360629632646270937, 360629636471091705⟩, ⟨(-1171960900224464000), (-1171895180513062764)⟩, true⟩

def words09 : List Nat := [360583492267678917, 360583493421206825, 360583495616545647, 360583496268264241, 360583496268570408, 360583495607467522, 360583495458174980, 360583497048432539, 360583498865215766, 360583500681929347]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 25390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 25300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 25300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk253B
