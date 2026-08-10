import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk749A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk749B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk749A

def state06 : KState := ⟨⟨360639778689588729, 360639815101800253⟩, ⟨(-4313519417648939226), (-4311675875670077546)⟩, true⟩

def words05 : List Nat := [360582291190813672, 360582291695355161, 360582292260045112, 360582292799161846, 360582293189464324, 360582293579855748, 360582294052830318, 360582294643641271, 360582295411852728, 360582296180285465]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360617385711719881, 360617422134115083⟩, ⟨(-2634960899413765914), (-2633116594019007092)⟩, true⟩

def words06 : List Nat := [360582296858974060, 360582297437479148, 360582298011686682, 360582298586176956, 360582299011968472, 360582299260165082, 360582299419268624, 360582299578484172, 360582299862699709, 360582300332431512]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579699944026891, 360579736376468944⟩, ⟨190573334783238510, 192418393441551660⟩, true⟩

def words07 : List Nat := [360582300800150055, 360582301268056122, 360582301626035778, 360582301908541288, 360582302145640427, 360582302383023065, 360582302616039011, 360582302671543998, 360582302672504908, 360582302639384943]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581980453436373, 360582016895952293⟩, ⟨19651726406980138, 21497540454571700⟩, true⟩

def words08 : List Nat := [360582302701615188, 360582302887895615, 360582303218042908, 360582303548409529, 360582303727162141, 360582303728334381, 360582303729205753, 360582303672983083, 360582303616439024, 360582303568047967]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586980938397462, 360587017391095317⟩, ⟨(-355415863147775415), (-353569285507084485)⟩, true⟩

def words09 : List Nat := [360582303565193119, 360582303425157984, 360582303284923682, 360582303272398707, 360582303273292617, 360582303256071921, 360582303238748932, 360582303108661777, 360582303132735904, 360582303196811147]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk749B
