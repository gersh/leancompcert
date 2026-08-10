import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk649A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk649B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk649A

def state06 : KState := ⟨⟨360571579347713121, 360571606383414268⟩, ⟨735915737386549584, 737102096884273850⟩, true⟩

def words05 : List Nat := [360582951777212733, 360582952403498838, 360582952847089707, 360582953132034459, 360582953260489828, 360582953389178502, 360582953598310959, 360582953599225789, 360582953572167954, 360582953398452512]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 64950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 64900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595038658220069, 360595065702552900⟩, ⟨(-788171666538443709), (-786984746284123395)⟩, true⟩

def words06 : List Nat := [360582953224523100, 360582953016923893, 360582953033635818, 360582953138103970, 360582953138948027, 360582953027291403, 360582952879155826, 360582952725490819, 360582952653332766, 360582952840717865]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 64960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 64900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593154612133019, 360593181665193802⟩, ⟨(-665750498292714515), (-664563010943387061)⟩, true⟩

def words07 : List Nat := [360582952909175710, 360582952977724135, 360582953197003017, 360582953625711301, 360582953926307247, 360582954227041912, 360582954348813559, 360582954349728910, 360582954470987374, 360582954629430373]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 64970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 64900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360572311901300348, 360572338962987824⟩, ⟨688634312514425670, 689822360469837202⟩, true⟩

def words08 : List Nat := [360582954781835990, 360582954782751175, 360582954699132912, 360582954497093592, 360582954294911614, 360582953978784472, 360582953780971422, 360582953653370718, 360582953525661131, 360582953247654232]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 64980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 64900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581152792616506, 360581179862944124⟩, ⟨114003410155449166, 115192019676196994⟩, true⟩

def words09 : List Nat := [360582953085077007, 360582953003549253, 360582953019974291, 360582953020889642, 360582952883954006, 360582952523570403, 360582952163022661, 360582952073426982, 360582952074173812, 360582952047862220]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 64990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 64900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 64900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk649B
