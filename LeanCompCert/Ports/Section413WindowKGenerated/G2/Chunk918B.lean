import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk918A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk918B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk918A

def state06 : KState := ⟨⟨360600020882508802, 360600076436979378⟩, ⟨(-1667155890948271251), (-1663709827045881107)⟩, true⟩

def words05 : List Nat := [360581963695634262, 360581963778918799, 360581963934491124, 360581964181604265, 360581964398680473, 360581964615968740, 360581964762191034, 360581964873987962, 360581965072226230, 360581965270901871]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592033008798968, 360592088575786263⟩, ⟨(-933421322393276758), (-929974108642004046)⟩, true⟩

def words06 : List Nat := [360581965407758834, 360581965490800047, 360581965500222452, 360581965509778258, 360581965510891991, 360581965487907395, 360581965631321835, 360581965775014714, 360581965856346120, 360581965967905191]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606499632314200, 360606555211834753⟩, ⟨(-2262602173446338751), (-2259153808203457187)⟩, true⟩

def words07 : List Nat := [360581966068366128, 360581966169234519, 360581966388021065, 360581966522699491, 360581966545245573, 360581966567871391, 360581966679455830, 360581966850694582, 360581967119382067, 360581967388365228]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584718240935339, 360584773833139321⟩, ⟨(-261266955324311698), (-257817424668419572)⟩, true⟩

def words08 : List Nat := [360581967582071849, 360581967778958996, 360581967993637712, 360581968208706069, 360581968321168414, 360581968322496880, 360581968316850161, 360581968250514768, 360581968183944860, 360581968145698022]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360568861062734271, 360568916667443039⟩, ⟨1195990339687642583, 1199441019473461079⟩, true⟩

def words09 : List Nat := [360581968253522055, 360581968361598086, 360581968410072243, 360581968440307887, 360581968441419633, 360581968442207538, 360581968477593779, 360581968478922404, 360581968396982230, 360581968256338289]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk918B
