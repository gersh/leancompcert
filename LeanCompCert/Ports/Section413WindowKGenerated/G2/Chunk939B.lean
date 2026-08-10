import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk939A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk939B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk939A

def state06 : KState := ⟨⟨360584075083729934, 360584133309863013⟩, ⟨(-198633311579935305), (-194939012336944821)⟩, true⟩

def words05 : List Nat := [360582057859798730, 360582057913240865, 360582058043185731, 360582058261652220, 360582058392646986, 360582058523856717, 360582058598081952, 360582058599442586, 360582058606161173, 360582058629811322]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584403974409042, 360584462213365879⟩, ⟨(-229581166679517981), (-225885662450359493)⟩, true⟩

def words06 : List Nat := [360582058630931121, 360582058626253415, 360582058603595876, 360582058524275669, 360582058444728485, 360582058337040994, 360582058345757120, 360582058407533123, 360582058408756945, 360582058432811769]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602920597879017, 360602978849680095⟩, ⟨(-1969711382505094160), (-1966014671240530968)⟩, true⟩

def words07 : List Nat := [360582058572652311, 360582058712890371, 360582058869912474, 360582058977253777, 360582058978532022, 360582058979288586, 360582059012945269, 360582059123921447, 360582059347618913, 360582059571621333]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595555359286840, 360595613624060632⟩, ⟨(-1277496294941316086), (-1273798364437325692)⟩, true⟩

def words08 : List Nat := [360582059738637020, 360582059918175993, 360582060210556714, 360582060503341337, 360582060767260248, 360582060918540708, 360582061002143890, 360582061085881145, 360582061134316403, 360582061280065598]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576642725977074, 360576701003564991⟩, ⟨500223152995349140, 503922287962423732⟩, true⟩

def words09 : List Nat := [360582061520446432, 360582061761084200, 360582061906544672, 360582061939306919, 360582061940453563, 360582061900693797, 360582061932293347, 360582061933655000, 360582061934588774, 360582061878968847]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk939B
