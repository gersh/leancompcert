import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk437A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk437B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk437A

def state06 : KState := ⟨⟨360598576449404682, 360598588331714381⟩, ⟨(-673477677001240255), (-673126286592425389)⟩, true⟩

def words05 : List Nat := [360583207214227944, 360583207091365048, 360583207366666000, 360583207392283345, 360583207392834218, 360583206977950841, 360583206562981787, 360583205921560372, 360583206103340209, 360583206455464012]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360559799471402347, 360559811359397073⟩, ⟨1023471666452037491, 1023823305666513879⟩, true⟩

def words06 : List Nat := [360583206486443513, 360583206487041081, 360583205997361824, 360583205910777836, 360583205824028478, 360583205603817006, 360583205015359461, 360583204169078157, 360583203322725150, 360583202341934577]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360524874444185375, 360524886337817951⟩, ⟨2552200790344369363, 2552552676355586665⟩, true⟩

def words07 : List Nat := [360583201808034309, 360583200967919548, 360583200127777494, 360583199025317373, 360583197602276336, 360583195834150515, 360583194065922980, 360583192819211373, 360583191750209496, 360583190419050377]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594730130799528, 360594742030066574⟩, ⟨(-506430400315931302), (-506078267599457482)⟩, true⟩

def words08 : List Nat := [360583189087812657, 360583188278031715, 360583187730521092, 360583187704349818, 360583187678144992, 360583187160238469, 360583186122215353, 360583185605540797, 360583185092530186, 360583185357060718]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571396374723636, 360571408279693595⟩, ⟨515536052810476365, 515888435285448941⟩, true⟩

def words09 : List Nat := [360583185357596880, 360583185229302606, 360583185493040713, 360583186155371361, 360583186570731018, 360583186986168185, 360583187076681899, 360583187077280018, 360583186822705751, 360583186554471802]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk437B
