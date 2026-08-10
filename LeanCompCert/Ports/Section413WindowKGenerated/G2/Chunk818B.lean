import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk818A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk818B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk818A

def state06 : KState := ⟨⟨360598354603010579, 360598398327918349⟩, ⟨(-1321755815405415566), (-1319338489919657358)⟩, true⟩

def words05 : List Nat := [360582281050176323, 360582281083875258, 360582281266362660, 360582281300177533, 360582281301272201, 360582281191852504, 360582281082212248, 360582281118242003, 360582281316077522, 360582281514174080]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594246468237127, 360594290204305767⟩, ⟨(-985529266197726682), (-983111027026945750)⟩, true⟩

def words06 : List Nat := [360582281617831960, 360582281727089390, 360582281943842441, 360582282160947707, 360582282275114479, 360582282276287260, 360582282241637386, 360582282114100549, 360582282006717387, 360582282154727444]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567841339327817, 360567885086462267⟩, ⟨1176436319991228144, 1178855465173822408⟩, true⟩

def words07 : List Nat := [360582282312613534, 360582282470741808, 360582282514193161, 360582282568794458, 360582282573785393, 360582282579085983, 360582282671590358, 360582282672763306, 360582282616544516, 360582282441923599]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596416911704325, 360596460669910950⟩, ⟨(-1163458141103966214), (-1161038089276031986)⟩, true⟩

def words08 : List Nat := [360582282267039676, 360582282178755161, 360582282299178929, 360582282434608322, 360582282437751262, 360582282444591875, 360582282495527737, 360582282546802266, 360582282648309576, 360582282822659408]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581703973246347, 360581747742652668⟩, ⟨41436649486000485, 43857618509476901⟩, true⟩

def words09 : List Nat := [360582282917963058, 360582283013381635, 360582283104619685, 360582283270977421, 360582283339867420, 360582283408941512, 360582283409986838, 360582283404421054, 360582283249866271, 360582283244710171]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk818B
