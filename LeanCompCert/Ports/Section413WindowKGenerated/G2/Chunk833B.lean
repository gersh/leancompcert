import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk833A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk833B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk833A

def state06 : KState := ⟨⟨360591607031888884, 360591652437981911⟩, ⟨(-770436739741987980), (-767880527610154258)⟩, true⟩

def words05 : List Nat := [360582441367039566, 360582441355834364, 360582441344278944, 360582441336003941, 360582441228600345, 360582440998878448, 360582440768906289, 360582440706657686, 360582440818130555, 360582440929871282]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360558411688876942, 360558457106372220⟩, ⟨1996812713156275375, 1999369875836495735⟩, true⟩

def words06 : List Nat := [360582440948939816, 360582440950135766, 360582440825536149, 360582440697441171, 360582440569032166, 360582440404639913, 360582440136596836, 360582439776056645, 360582439415304204, 360582438992852207]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360525034885026589, 360525080313778320⟩, ⟨4779673059472332661, 4782231160659928643⟩, true⟩

def words07 : List Nat := [360582438706166446, 360582438539170396, 360582438372045316, 360582438132944060, 360582437750116579, 360582437269413913, 360582436788375212, 360582436270467325, 360582435655731507, 360582434969099260]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360559755450763729, 360559800890795791⟩, ⟨1884502727537515759, 1887061769335250673⟩, true⟩

def words08 : List Nat := [360582434282203820, 360582433716381786, 360582433240488369, 360582432908578951, 360582432576577078, 360582432110935922, 360582431532344019, 360582431055149924, 360582430577615934, 360582430244067590]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360570280818017243, 360570326269459759⟩, ⟨1006665590922071377, 1009225584291261715⟩, true⟩

def words09 : List Nat := [360582429973797167, 360582429568634944, 360582429163253256, 360582428867281507, 360582428659662232, 360582428372884691, 360582428085983528, 360582427727187114, 360582427439381816, 360582427295650302]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk833B
