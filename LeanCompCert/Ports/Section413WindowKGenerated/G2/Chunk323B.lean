import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk323A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk323B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk323A

def state06 : KState := ⟨⟨360587026182821652, 360587032521613273⟩, ⟨(-179224185831663261), (-179085483854621945)⟩, true⟩

def words05 : List Nat := [360581505456984393, 360581504207728215, 360581502958423248, 360581502661045285, 360581502395419881, 360581501314403729, 360581500233374428, 360581498968289044, 360581498359119661, 360581498530579170]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 32350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 32300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589287642504859, 360589293985410858⟩, ⟨(-252669795801194892), (-252530960663107570)⟩, true⟩

def words06 : List Nat := [360581498530970630, 360581497855135110, 360581497199383356, 360581497347481375, 360581497347842444, 360581497255747831, 360581496210624020, 360581494688844978, 360581493167069014, 360581492837449316]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 32360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 32300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360522156161810078, 360522162508774560⟩, ⟨1920864579298663330, 1921003545830550630⟩, true⟩

def words07 : List Nat := [360581494029642189, 360581495221843894, 360581495697469359, 360581495697900823, 360581495220906768, 360581493977225443, 360581492733493751, 360581492440487387, 360581491195002473, 360581489363185634]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 32370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 32300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360552057971453117, 360552064322497961⟩, ⟨952591134203523697, 952730232877371989⟩, true⟩

def words08 : List Nat := [360581487531384528, 360581486650268427, 360581486521464000, 360581486297900086, 360581486074313916, 360581484923619269, 360581482820816207, 360581481443775230, 360581480066699211, 360581478655096831]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 32380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 32300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360528033626500372, 360528039981660209⟩, ⟨1730819359016709021, 1730958590995177865⟩, true⟩

def words09 : List Nat := [360581477747383121, 360581476200191594, 360581474653013420, 360581473620079017, 360581473070449766, 360581471762482334, 360581470454539102, 360581468671002720, 360581466277992538, 360581464629530431]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 32390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 32300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 32300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk323B
