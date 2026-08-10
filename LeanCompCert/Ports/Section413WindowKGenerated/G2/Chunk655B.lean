import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk655A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk655B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk655A

def state06 : KState := ⟨⟨360569145828347719, 360569173386092866⟩, ⟨898861034428996767, 900081462740296687⟩, true⟩

def words05 : List Nat := [360582901850681882, 360582902252845467, 360582902538477857, 360582902656241415, 360582902657028118, 360582902614778523, 360582902761228104, 360582902762152055, 360582902719969531, 360582902511515995]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585849378479706, 360585876944951147⟩, ⟨(-196189828914062558), (-194968828464970386)⟩, true⟩

def words06 : List Nat := [360582902302853308, 360582902396996070, 360582902771467118, 360582903146104138, 360582903326502962, 360582903327426951, 360582903411382623, 360582903548013736, 360582903548778290, 360582903544690896]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360573736052734546, 360573763628003738⟩, ⟨598116155361955899, 599337732724022069⟩, true⟩

def words07 : List Nat := [360582903545519828, 360582903413075656, 360582903280455233, 360582903351838839, 360582903352613673, 360582903330309565, 360582903307889344, 360582903169234354, 360582902798524858, 360582902660219719]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595727032086493, 360595754616073080⟩, ⟨(-844193675753819314), (-842971526661347818)⟩, true⟩

def words08 : List Nat := [360582902614340808, 360582902687382769, 360582902688229140, 360582902575379753, 360582902462386839, 360582902220574503, 360582902292024014, 360582902444322687, 360582902480221518, 360582902677138450]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602630284489461, 360602657877198391⟩, ⟨(-1297077275851699102), (-1295854554617793136)⟩, true⟩

def words09 : List Nat := [360582903056154107, 360582903435438744, 360582903778152943, 360582903889225226, 360582903890077738, 360582903803545689, 360582903716850338, 360582903693955859, 360582903995834207, 360582904297914268]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk655B
