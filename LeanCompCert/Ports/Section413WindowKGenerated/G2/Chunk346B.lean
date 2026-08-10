import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk346A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk346B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk346A

def state06 : KState := ⟨⟨360578757014945358, 360578764328430037⟩, ⟨101559886773446618, 101731264460959424⟩, true⟩

def words05 : List Nat := [360581694682886051, 360581696543278714, 360581697984380203, 360581698596370256, 360581698805639290, 360581699015019830, 360581699199610377, 360581699532369750, 360581699532787064, 360581699448581825]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 34650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 34600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595799553366939, 360595806871231474⟩, ⟨(-489315203332468323), (-489143673817291431)⟩, true⟩

def words06 : List Nat := [360581699364279542, 360581699204717495, 360581699633605965, 360581700062565617, 360581700062993565, 360581699783975860, 360581698676129681, 360581698399650104, 360581698313675097, 360581698721082437]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 34660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 34600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360614886638574694, 360614893960868343⟩, ⟨(-1151273073679874275), (-1151101390585299771)⟩, true⟩

def words07 : List Nat := [360581698721505239, 360581698432691756, 360581698685401324, 360581699645615223, 360581700167177338, 360581700688783941, 360581700794221749, 360581700921218376, 360581701878717434, 360581702836316419]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 34670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 34600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360604604672641976, 360604611999308684⟩, ⟨(-794737481258406939), (-794565646484209499)⟩, true⟩

def words08 : List Nat := [360581704395418458, 360581705126668072, 360581705233865474, 360581705341108026, 360581705341503570, 360581704964461657, 360581705885935038, 360581706807444258, 360581707252604508, 360581707913335832]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 34680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 34600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360646924887872427, 360646932218933122⟩, ⟨(-2262908517061643813), (-2262736529838732223)⟩, true⟩

def words09 : List Nat := [360581709216912165, 360581710520558421, 360581712654024722, 360581715046098373, 360581716723891822, 360581718401620709, 360581719888888003, 360581721793277607, 360581723672923003, 360581725552559279]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 34690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 34600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 34600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk346B
