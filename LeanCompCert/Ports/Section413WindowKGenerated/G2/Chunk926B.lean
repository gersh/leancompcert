import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk926A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk926B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk926A

def state06 : KState := ⟨⟨360592332412802575, 360592388977382075⟩, ⟨(-966510059719403765), (-962970802608558957)⟩, true⟩

def words05 : List Nat := [360581995675960132, 360581995857101833, 360581996055495977, 360581996137931514, 360581996139180442, 360581996117986185, 360581996190357526, 360581996343817077, 360581996457079496, 360581996570624016]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 92650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 92600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588868489507896, 360588925066856340⟩, ⟨(-645639684474820339), (-642099244132073133)⟩, true⟩

def words06 : List Nat := [360581996614630393, 360581996615970823, 360581996572858834, 360581996577702984, 360581996578825076, 360581996532749302, 360581996489387469, 360581996350022989, 360581996210404577, 360581996262331386]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 92660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 92600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562738082872275, 360562794672856018⟩, ⟨1776049755061983996, 1779591366382762290⟩, true⟩

def words07 : List Nat := [360581996454507240, 360581996646935986, 360581996748303774, 360581996749644348, 360581996734765396, 360581996640614734, 360581996546077477, 360581996486767513, 360581996339204537, 360581996133434167]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 92670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 92600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595541793098403, 360595598395739122⟩, ⟨(-1264350751877176626), (-1260807967448101294)⟩, true⟩

def words08 : List Nat := [360581995927339835, 360581995837959432, 360581995917537814, 360581996016277202, 360581996017514376, 360581996005615164, 360581995981136230, 360581995954422584, 360581995978034876, 360581996126182768]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 92680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 92600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598133878283773, 360598190493696106⟩, ⟨(-1504611486062987237), (-1501067517769400087)⟩, true⟩

def words09 : List Nat := [360581996214670882, 360581996303291078, 360581996507919573, 360581996803288379, 360581997069179214, 360581997335283189, 360581997511007887, 360581997570778359, 360581997746543095, 360581997922766242]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 92690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 92600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 92600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk926B
