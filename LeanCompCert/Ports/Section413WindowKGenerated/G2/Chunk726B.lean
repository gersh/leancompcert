import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk726A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk726B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk726A

def state06 : KState := ⟨⟨360573113360117664, 360573147487938383⟩, ⟨669300110473225353, 670975027141582979⟩, true⟩

def words05 : List Nat := [360582382728056425, 360582382727202382, 360582382726165116, 360582382717514402, 360582382718383987, 360582382639726311, 360582382560971551, 360582382343323046, 360582382062321873, 360582381936426432]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578311049752467, 360578345187287589⟩, ⟨291595238330362013, 293270860895703719⟩, true⟩

def words06 : List Nat := [360582381872147264, 360582381873179576, 360582381809780678, 360582381638387719, 360582381466830525, 360582381247512274, 360582381175155063, 360582381094762353, 360582381014258985, 360582380839701181]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360620693920625707, 360620728067899346⟩, ⟨(-2788573384687511399), (-2786897054376272413)⟩, true⟩

def words07 : List Nat := [360582380918481477, 360582381053094076, 360582381376405637, 360582381765965611, 360582381980881473, 360582382195856835, 360582382440050677, 360582382779813356, 360582383308238555, 360582383836884690]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601614270456331, 360601648427571594⟩, ⟨(-1401931342157610934), (-1400254296507299712)⟩, true⟩

def words08 : List Nat := [360582384217758953, 360582384409792091, 360582384657806476, 360582384906124597, 360582385106141051, 360582385117403585, 360582385118323459, 360582385035447585, 360582385057340543, 360582385323521474]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578048604438562, 360578082771274004⟩, ⟨311245423660089000, 312923175918544570⟩, true⟩

def words09 : List Nat := [360582385742246824, 360582386161161063, 360582386464669572, 360582386686267582, 360582386756410232, 360582386826814078, 360582387049379604, 360582387136269248, 360582387137195542, 360582387079058304]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk726B
