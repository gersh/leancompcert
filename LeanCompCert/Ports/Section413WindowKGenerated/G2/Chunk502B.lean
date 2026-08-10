import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk502A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk502B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk502A

def state06 : KState := ⟨⟨360563600117096653, 360563615970796145⟩, ⟨920713840738896648, 921252246923159780⟩, true⟩

def words05 : List Nat := [360581944995734514, 360581945799957581, 360581946299832455, 360581946404803633, 360581946405386332, 360581946241211306, 360581946126860468, 360581946127557600, 360581946065111679, 360581945701136837]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599475773463703, 360599491633705226⟩, ⟨(-882496969103350668), (-881958234083737104)⟩, true⟩

def words06 : List Nat := [360581945367358836, 360581945598051520, 360581946223544304, 360581946849145273, 360581947141555300, 360581947210961864, 360581947211532875, 360581947165799370, 360581947208194283, 360581947557914338]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360613586844740761, 360613602711587865⟩, ⟨(-1591940618448035476), (-1591401551334226462)⟩, true⟩

def words07 : List Nat := [360581947655772327, 360581947753699412, 360581948246370398, 360581949055603400, 360581949759502493, 360581950463486176, 360581950969423430, 360581951294110537, 360581951924174887, 360581952554444328]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360604720431910741, 360604736305302717⟩, ⟨(-1146254238701852826), (-1145714842479775472)⟩, true⟩

def words08 : List Nat := [360581952979568625, 360581953175193101, 360581953175817528, 360581953105315436, 360581953034699742, 360581952896864170, 360581953378544599, 360581953860350808, 360581954144264111, 360581954597989684]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360621516610641449, 360621532490585214⟩, ⟨(-1991039154858956242), (-1990499429115018416)⟩, true⟩

def words09 : List Nat := [360581955446155536, 360581956294503418, 360581957313152915, 360581957937635787, 360581958193237997, 360581958448873295, 360581958682145125, 360581959149294957, 360581959936602833, 360581960724037531]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk502B
