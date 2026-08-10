import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk672A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk672B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk672A

def state06 : KState := ⟨⟨360565740155720401, 360565769220403097⟩, ⟨1154228720149860847, 1155549229946122147⟩, true⟩

def words05 : List Nat := [360582951476036946, 360582951118466493, 360582950760720666, 360582950581869436, 360582950570781198, 360582950504328584, 360582950437767086, 360582950233482611, 360582949808234379, 360582949553884307]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 67250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 67200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578440883467865, 360578469957106237⟩, ⟨299891250973890138, 301212363172926572⟩, true⟩

def words06 : List Nat := [360582949299224128, 360582949265403553, 360582949176109344, 360582948915267534, 360582948654284039, 360582948248593313, 360582947997518021, 360582947922961901, 360582947848306653, 360582947619707292]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 67260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 67200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592791564541973, 360592820647140250⟩, ⟨(-665524449669132201), (-664202734693529365)⟩, true⟩

def words07 : List Nat := [360582947707948089, 360582947863024430, 360582948238405167, 360582948393260369, 360582948394150869, 360582948343285991, 360582948292247964, 360582948282023903, 360582948429528922, 360582948577243942]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 67270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 67200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586525173139967, 360586554264783524⟩, ⟨(-244048099170745301), (-242725775584245651)⟩, true⟩

def words08 : List Nat := [360582948581789335, 360582948582739113, 360582948366558879, 360582948307611853, 360582948248385831, 360582948133828742, 360582947947679256, 360582947593332263, 360582947238809461, 360582947158698249]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 67280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 67200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574664455467994, 360574693556064996⟩, ⟨554054808454078736, 555377734562766312⟩, true⟩

def words09 : List Nat := [360582947208130286, 360582947257729368, 360582947258583647, 360582947196573325, 360582946913833022, 360582946535317476, 360582946156534573, 360582945958620676, 360582945947160022, 360582945825523581]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 67290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 67200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 67200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk672B
