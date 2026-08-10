import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk900A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk900B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk900A

def state06 : KState := ⟨⟨360582680001373607, 360582733317812911⟩, ⟨(-71421550068410559), (-68179064712173567)⟩, true⟩

def words05 : List Nat := [360581976192689236, 360581976149039169, 360581976183377754, 360581976325041919, 360581976374179727, 360581976423508689, 360581976424674295, 360581976381168551, 360581976275857081, 360581976285748953]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360597083190900200, 360597136519595423⟩, ⟨(-1368629232814062233), (-1365385643628515339)⟩, true⟩

def words06 : List Nat := [360581976395868403, 360581976511965217, 360581976566463605, 360581976621097907, 360581976644548434, 360581976754104424, 360581976986419533, 360581977218989517, 360581977357112710, 360581977526760565]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606850051184264, 360606903392145491⟩, ⟨(-2248325779736275404), (-2245081085690534150)⟩, true⟩

def words07 : List Nat := [360581977819250596, 360581978112131039, 360581978527746301, 360581978877506300, 360581979122009062, 360581979366628705, 360581979612977539, 360581979921609794, 360581980199351272, 360581980477372226]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593673307107365, 360593726660480358⟩, ⟨(-1061438022129782612), (-1058192209976046308)⟩, true⟩

def words08 : List Nat := [360581980693822912, 360581980820514123, 360581980894390940, 360581980968626846, 360581980988299196, 360581980989600113, 360581980936499809, 360581980821700740, 360581980713663105, 360581980845582355]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360564291647250830, 360564345012850654⟩, ⟨1585747690300033487, 1588994604029098967⟩, true⟩

def words09 : List Nat := [360581981035105449, 360581981224872189, 360581981340310507, 360581981361463011, 360581981362551459, 360581981325725341, 360581981288536623, 360581981224744234, 360581981107393959, 360581980913006360]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk900B
