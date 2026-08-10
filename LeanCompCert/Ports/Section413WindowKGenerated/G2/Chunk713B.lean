import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk713A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk713B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk713A

def state06 : KState := ⟨⟨360592238686364465, 360592271556644668⟩, ⟨(-713039885967887993), (-711455527369128845)⟩, true⟩

def words05 : List Nat := [360582301698304807, 360582301737084426, 360582301971606894, 360582302010253935, 360582302011187699, 360582301869672285, 360582301727976666, 360582301522840616, 360582301607063219, 360582301747822355]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581546914631002, 360581579794561082⟩, ⟨49910424418476169, 51495471678423557⟩, true⟩

def words06 : List Nat := [360582301788663938, 360582301789676841, 360582301833467490, 360582301954073251, 360582301954935287, 360582301940165544, 360582301860018749, 360582301681965492, 360582301503718682, 360582301322817751]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360556139408191030, 360556172297660870⟩, ⟨1863448810229806278, 1865034538389614158⟩, true⟩

def words07 : List Nat := [360582301458998406, 360582301605495838, 360582301625289899, 360582301626302286, 360582301495694069, 360582301309069868, 360582301122154060, 360582301090024449, 360582300913409935, 360582300548408834]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592688708613177, 360592721607640615⟩, ⟨(-745719797783179369), (-744133387354251565)⟩, true⟩

def words08 : List Nat := [360582300183188544, 360582299935707848, 360582299786773220, 360582299551754765, 360582299316664420, 360582298914642149, 360582298517838202, 360582298317232194, 360582298116323395, 360582298257535501]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582554139880434, 360582587048562397⟩, ⟨(-22215755477546634), (-20628655766012108)⟩, true⟩

def words09 : List Nat := [360582298292257846, 360582298327090775, 360582298327924975, 360582298380198249, 360582298391704739, 360582298403380643, 360582298404291456, 360582298317560994, 360582298130635428, 360582298135861371]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk713B
