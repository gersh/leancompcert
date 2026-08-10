import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk378A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk378B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk378A

def state06 : KState := ⟨⟨360570874506833001, 360570883296520306⟩, ⟨408543436434343643, 408768378620442609⟩, true⟩

def words05 : List Nat := [360581681052865965, 360581680493963589, 360581680072555809, 360581680565863268, 360581680781764216, 360581680997748227, 360581680998203161, 360581680864317807, 360581680421552177, 360581680136948739]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591935186655652, 360591943981157800⟩, ⟨(-388928500042113345), (-388703375541162309)⟩, true⟩

def words06 : List Nat := [360581680263697262, 360581680571661566, 360581680572128657, 360581680330667660, 360581680089136134, 360581679670739253, 360581679825757036, 360581680051445246, 360581680051902402, 360581680101789916]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360625566907791052, 360625575707110485⟩, ⟨(-1662785621866674281), (-1662560314911202321)⟩, true⟩

def words07 : List Nat := [360581681069508401, 360581682037330587, 360581683081543964, 360581683759250489, 360581683814485876, 360581683869759092, 360581683896397811, 360581684359646476, 360581685518754073, 360581686677916135]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360644225602382319, 360644234406573253⟩, ⟨(-2369877149698425555), (-2369651658187641579)⟩, true⟩

def words08 : List Nat := [360581687358727766, 360581688138588933, 360581689351641445, 360581690564793163, 360581691601065818, 360581692345646669, 360581692703269457, 360581693060929502, 360581694114135632, 360581695765255061]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589824297290780, 360589833106299384⟩, ⟨(-308408083288463498), (-308182409211351904)⟩, true⟩

def words09 : List Nat := [360581697395165384, 360581699025080420, 360581700171603499, 360581700625214769, 360581700625647536, 360581700473984856, 360581700865345210, 360581701428769522, 360581701643785218, 360581701858859703]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk378B
