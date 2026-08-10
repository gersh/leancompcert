import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk427A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk427B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk427A

def state06 : KState := ⟨⟨360612620271867013, 360612631595788579⟩, ⟨(-1277106198587449470), (-1276778965172228736)⟩, true⟩

def words05 : List Nat := [360582757745830580, 360582760715161109, 360582763408837109, 360582765558191400, 360582767386105711, 360582769214098442, 360582770732301271, 360582771706329895, 360582772405167447, 360582773104051430]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 42750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 42700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360642070465163730, 360642081794594608⟩, ⟨(-2536623910674183939), (-2536296441653790183)⟩, true⟩

def words06 : List Nat := [360582774180977853, 360582775530612863, 360582776678865964, 360582777827168550, 360582778514987393, 360582778658801690, 360582779349321927, 360582780039991475, 360582780965321040, 360582782352410563]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 42760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 42700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360616668461012754, 360616679795990768⟩, ⟨(-1449973454675031687), (-1449645748377165051)⟩, true⟩

def words07 : List Nat := [360582783421929718, 360582784491464239, 360582786107526141, 360582787995978293, 360582789561964677, 360582791127971834, 360582792229744167, 360582792940356627, 360582793732950318, 360582794525698415]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 42770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 42700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360621735461449976, 360621746801918692⟩, ⟨(-1666862106104094145), (-1666534164885977771)⟩, true⟩

def words08 : List Nat := [360582795742385919, 360582796415588443, 360582796749880022, 360582797084227257, 360582797192309845, 360582797576811282, 360582798507466454, 360582799438190958, 360582799987455360, 360582800898226655]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 42780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 42700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360660255454018614, 360660266799995162⟩, ⟨(-3315475421521616437), (-3315147244595827273)⟩, true⟩

def words09 : List Nat := [360582801793819892, 360582802689533968, 360582804131251843, 360582805029689120, 360582805462780433, 360582805895894271, 360582806875013415, 360582808277818172, 360582810088068408, 360582811898366793]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 42790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 42700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 42700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk427B
