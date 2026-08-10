import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk725A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk725B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk725A

def state06 : KState := ⟨⟨360592258775176389, 360592292805328719⟩, ⟨(-720536999118561087), (-718869174148079921)⟩, true⟩

def words05 : List Nat := [360582385995174494, 360582386066463001, 360582386193923818, 360582386194954061, 360582386132894780, 360582385893583127, 360582385654071668, 360582385482167407, 360582385566470733, 360582385704073940]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589054039827429, 360589088079804222⟩, ⟨(-488029748702144391), (-486361210820916415)⟩, true⟩

def words06 : List Nat := [360582385713384511, 360582385777955249, 360582385992741282, 360582386207823717, 360582386322852590, 360582386381939983, 360582386382873060, 360582386298146374, 360582386213239214, 360582386212518104]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360576536367476803, 360576570417162918⟩, ⟨420456106134148981, 422125348670783549⟩, true⟩

def words07 : List Nat := [360582386420049260, 360582386627771406, 360582386699489457, 360582386700520074, 360582386627344157, 360582386506957309, 360582386454210200, 360582386496250596, 360582386497173299, 360582386418109058]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591882800011186, 360591916859434909⟩, ⟨(-693473794399402005), (-691803845059227899)⟩, true⟩

def words08 : List Nat := [360582386416792748, 360582386591605423, 360582386762267831, 360582386933108781, 360582386943821826, 360582386944852521, 360582386765984869, 360582386690351656, 360582386614422096, 360582386699428032]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583202968074931, 360583237037313136⟩, ⟨(-63319868571152727), (-61649206749803143)⟩, true⟩

def words09 : List Nat := [360582386737207826, 360582386775103828, 360582386966900401, 360582387281469053, 360582387547611622, 360582387813914967, 360582387932093077, 360582387933123976, 360582387873500524, 360582387886382023]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk725B
