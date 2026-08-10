import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk867A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk867B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk867A

def state06 : KState := ⟨⟨360594524008782334, 360594573346840000⟩, ⟨(-1077890686505761467), (-1074999973903185107)⟩, true⟩

def words05 : List Nat := [360582182125879010, 360582182090036713, 360582182149582916, 360582182326856908, 360582182470328093, 360582182614001975, 360582182654718794, 360582182699343801, 360582182843167879, 360582182987416951]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601237571681331, 360601286921487996⟩, ⟨(-1660388129390849079), (-1657496397386259573)⟩, true⟩

def words06 : List Nat := [360582183224760341, 360582183471071508, 360582183650777447, 360582183830615582, 360582183893936821, 360582184024474067, 360582184287304367, 360582184550380920, 360582184737443781, 360582184958880832]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607671375019856, 360607720736628611⟩, ⟨(-2218637445202452911), (-2215744689073175119)⟩, true⟩

def words07 : List Nat := [360582185312683050, 360582185666867785, 360582186079305007, 360582186409108764, 360582186623518495, 360582186838013406, 360582187157679748, 360582187544369192, 360582187839633636, 360582188135148182]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608932653411849, 360608982026904252⟩, ⟨(-2328210427505842426), (-2325316640053412598)⟩, true⟩

def words08 : List Nat := [360582188364063723, 360582188460415790, 360582188689138020, 360582188918221780, 360582189068844825, 360582189223397017, 360582189311447586, 360582189399627908, 360582189576570012, 360582189886704769]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578332775128189, 360578382160384663⟩, ⟨327769663605888847, 330664472122189131⟩, true⟩

def words09 : List Nat := [360582190304144187, 360582190721816068, 360582191037613312, 360582191220865148, 360582191370489525, 360582191520454533, 360582191676619537, 360582191700369969, 360582191701482361, 360582191658911417]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk867B
