import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk854A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk854B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk854A

def state06 : KState := ⟨⟨362486341010598424, 362486451084136774⟩, ⟨(-106160588915902969), (-99808938773310033)⟩, true⟩

def words05 : List Nat := [371285283142141786, 371285283149548246, 371285283292279999, 371285283295249434, 371285283255775391, 371285283193688858, 371285283179029371, 371285283182301953, 371285283178432278, 371285283195406555]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479576807422737, 362479686907802308⟩, ⟨471894541087142097, 478248485214447603⟩, true⟩

def words06 : List Nat := [371285283205899397, 371285283208889907, 371285283124234775, 371285283070785543, 371285283015808261, 371285283003586046, 371285282822705279, 371285282643399369, 371285282462910926, 371285282420674830]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467474137660389, 362467584264770238⟩, ⟨1506427888173282194, 1512784117076714086⟩, true⟩

def words07 : List Nat := [371285282416758537, 371285282479558836, 371285282541697563, 371285282544668240, 371285282424234189, 371285282329469195, 371285282233223578, 371285282194429655, 371285281989701924, 371285281786027570]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473196780762788, 362473306934475024⟩, ⟨1017228335254123058, 1023586838261614460⟩, true⟩

def words08 : List Nat := [371285281581025884, 371285281421300880, 371285281192834583, 371285281088960263, 371285280984133760, 371285280849872129, 371285280532285404, 371285280353025873, 371285280172172397, 371285280110732617]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476684984161166, 362476795164972179⟩, ⟨718974963769767128, 725335783583194646⟩, true⟩

def words09 : List Nat := [371285279972965586, 371285279802209015, 371285279630254976, 371285279523754770, 371285279347837834, 371285279214985243, 371285279081105515, 371285278947945929, 371285278719957301, 371285278624429293]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk854B
