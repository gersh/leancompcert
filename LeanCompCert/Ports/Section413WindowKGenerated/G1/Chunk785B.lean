import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk785A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk785B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk785A

def state06 : KState := ⟨⟨362487089898037931, 362487182314231470⟩, ⟨(-158046934356564774), (-153144286659365122)⟩, true⟩

def words05 : List Nat := [371285233464965731, 371285233340119783, 371285233247621392, 371285233250383310, 371285233174848237, 371285233074095522, 371285232972269642, 371285232974032786, 371285232918493255, 371285232946394257]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 78550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 78500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480356617144558, 362480449057853288⟩, ⟨370907244222691162, 375811817956259834⟩, true⟩

def words06 : List Nat := [371285232948479367, 371285232930174141, 371285232765526118, 371285232751217291, 371285232754227892, 371285232756940925, 371285232577853498, 371285232399739033, 371285232220443996, 371285232204320849]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 78560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 78500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475251831485621, 362475344296577830⟩, ⟨772068904235208109, 776975393907135809⟩, true⟩

def words07 : List Nat := [371285232246284569, 371285232350216201, 371285232422156550, 371285232424877108, 371285232330945996, 371285232247908734, 371285232238973799, 371285232241687209, 371285232118468897, 371285231995660385]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 78570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 78500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486941161723457, 362487033651134994⟩, ⟨(-146472139572168520), (-141563738766302612)⟩, true⟩

def words08 : List Nat := [371285231895746009, 371285231898788137, 371285231992411192, 371285232122214800, 371285232245088459, 371285232247801963, 371285232201665406, 371285232251929940, 371285232353772120, 371285232379503812]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 78580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 78500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487701314674750, 362487793828840179⟩, ⟨(-206215276049483873), (-201304929713790291)⟩, true⟩

def words09 : List Nat := [371285232381541054, 371285232368187488, 371285232499144758, 371285232566692751, 371285232637887301, 371285232710133989, 371285232761908174, 371285232764635134, 371285232694027588, 371285232730002839]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 78590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 78500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 78500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk785B
