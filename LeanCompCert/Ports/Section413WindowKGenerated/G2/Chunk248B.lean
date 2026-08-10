import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk248A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk248B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk248A

def state06 : KState := ⟨⟨360667967232751652, 360667970889790165⟩, ⟨(-2092042696883809552), (-2091981193703218118)⟩, true⟩

def words05 : List Nat := [360583803379664446, 360583805522785383, 360583808503833429, 360583811347919551, 360583812824719302, 360583814301427081, 360583815242641125, 360583817013582997, 360583820398957286, 360583823784134592]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 24850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 24800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360609418538282579, 360609422198408565⟩, ⟨(-636497303200451630), (-636435723249617396)⟩, true⟩

def words06 : List Nat := [360583826353437127, 360583828004338731, 360583830040701602, 360583832077001183, 360583833698904692, 360583833715132431, 360583833715424592, 360583832887708933, 360583832059999174, 360583832727810294]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 24860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 24800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360522475654232387, 360522479317419084⟩, ⟨1525976744972366130, 1526038401058727412⟩, true⟩

def words07 : List Nat := [360583832728080564, 360583832278058479, 360583831828037248, 360583830563952297, 360583827694928758, 360583824386683484, 360583821078606244, 360583819382812193, 360583817731048992, 360583815266014693]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 24870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 24800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360645535606794947, 360645539273048498⟩, ⟨(-1536383078552645039), (-1536321346148381997)⟩, true⟩

def words08 : List Nat := [360583812801105396, 360583811684634631, 360583812978345600, 360583814272014600, 360583814272321994, 360583814070433118, 360583813192656238, 360583813207015587, 360583814831323578, 360583817311449994]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 24880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 24800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565614689097680, 360565618358449457⟩, ⟨453297440277689910, 453359249811943492⟩, true⟩

def words09 : List Nat := [360583818979031958, 360583820646521027, 360583821998016261, 360583824165999043, 360583825422888694, 360583826679729078, 360583826971212601, 360583826971537769, 360583826288108474, 360583825557237086]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 24890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 24800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 24800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk248B
