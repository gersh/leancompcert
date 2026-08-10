import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk332A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk332B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk332A

def state06 : KState := ⟨⟨360651902798585735, 360651909510182800⟩, ⟨(-2348605947523974017), (-2348455013014216859)⟩, true⟩

def words05 : List Nat := [360581288766147894, 360581290567341925, 360581292505833297, 360581294193231026, 360581295110033414, 360581296026811541, 360581296917854513, 360581298396191058, 360581300519554399, 360581302642890349]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360567262176537261, 360567268892366178⟩, ⟨466775669837368542, 466926745119572944⟩, true⟩

def words06 : List Nat := [360581304313377382, 360581305082887251, 360581305789598938, 360581306496414005, 360581306973095450, 360581306973539719, 360581306549401221, 360581305544874281, 360581304540324618, 360581303360208666]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360515351823037045, 360515358543054323⟩, ⟨2194032133005554367, 2194183347655876523⟩, true⟩

def words07 : List Nat := [360581302938751610, 360581302354618384, 360581301770475530, 360581300732250051, 360581299075113759, 360581296837194070, 360581294599278740, 360581293042342426, 360581291513764998, 360581289533068022]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360620393706774928, 360620400430986415⟩, ⟨(-1302366584076610645), (-1302215229822219011)⟩, true⟩

def words08 : List Nat := [360581287552388121, 360581285978755333, 360581284932343745, 360581284561201333, 360581284190053546, 360581282968401200, 360581282144423723, 360581282182819883, 360581283121129468, 360581284296601080]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360557802214795053, 360557808943249913⟩, ⟨781758214704892606, 781909710241418054⟩, true⟩

def words09 : List Nat := [360581284982795212, 360581285669000722, 360581286569235046, 360581287979051447, 360581289159575006, 360581290340100147, 360581290829412979, 360581290829857704, 360581290419966393, 360581289715329235]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk332B
