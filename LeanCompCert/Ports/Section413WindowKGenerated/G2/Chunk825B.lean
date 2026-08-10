import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk825A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk825B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk825A

def state06 : KState := ⟨⟨360583219161075295, 360583263666545261⟩, ⟨(-77018771342084463), (-74537275473857205)⟩, true⟩

def words05 : List Nat := [360582361400898217, 360582361295823415, 360582361190521914, 360582361228708926, 360582361229708243, 360582361165562393, 360582361101298909, 360582360963529205, 360582360839668075, 360582360851953943]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 82550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 82500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585624619188490, 360585669135802631⟩, ⟨(-275664754164753906), (-273182338178613356)⟩, true⟩

def words06 : List Nat := [360582361010527669, 360582361022961939, 360582361024022483, 360582360932485226, 360582360840774673, 360582360643569941, 360582360618455009, 360582360679933294, 360582360680990707, 360582360682009186]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 82560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 82500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360601818104833289, 360601862632635510⟩, ⟨(-1612786783487913134), (-1610303443647036744)⟩, true⟩

def words07 : List Nat := [360582360869687311, 360582361057731226, 360582361350846139, 360582361653362745, 360582361828995479, 360582362004710140, 360582362202358972, 360582362473693498, 360582362710804005, 360582362948160304]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 82570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 82500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605615441657704, 360605659980731762⟩, ⟨(-1926482300156933324), (-1923998029431744812)⟩, true⟩

def words08 : List Nat := [360582363111748454, 360582363163709839, 360582363334395778, 360582363505439184, 360582363626019227, 360582363815048945, 360582363930351214, 360582364045787919, 360582364204717956, 360582364488130489]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 82580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 82500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584353542874192, 360584398093110603⟩, ⟨(-170283237216706489), (-167798044537933673)⟩, true⟩

def words09 : List Nat := [360582364917715982, 360582365347519162, 360582365654888698, 360582365859136547, 360582366026319138, 360582366193811741, 360582366476359306, 360582366612881904, 360582366638538099, 360582366664380468]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 82590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 82500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 82500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk825B
