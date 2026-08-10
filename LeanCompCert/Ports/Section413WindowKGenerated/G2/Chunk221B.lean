import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk221A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk221B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk221A

def state06 : KState := ⟨⟨360709907421443927, 360709910297761930⟩, ⟨(-2879725622742709618), (-2879682496244589182)⟩, true⟩

def words05 : List Nat := [360579942076273860, 360579942038897458, 360579943997500080, 360579946703498947, 360579947467883094, 360579948232216576, 360579951029522689, 360579954861688430, 360579960726335295, 360579966590517465]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 22150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 22100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360639717790322563, 360639720669372731⟩, ⟨(-1324115967217930293), (-1324072780161337603)⟩, true⟩

def words06 : List Nat := [360579971299076239, 360579976073930416, 360579981944725269, 360579987815073832, 360579991929628548, 360579994019421651, 360579995051160043, 360579996082834882, 360579997043418739, 360579999737517545]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 22160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 22100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360595129326338047, 360595132208089698⟩, ⟨(-335218082549926877), (-335174835587717073)⟩, true⟩

def words07 : List Nat := [360580004461845350, 360580009185802154, 360580012673223482, 360580014136791403, 360580015062482708, 360580015988176212, 360580018239543176, 360580019946588339, 360580020628190197, 360580021309771872]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 22170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 22100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360634773573103477, 360634776457565243⟩, ⟨(-1214865506004958592), (-1214822198918914190)⟩, true⟩

def words08 : List Nat := [360580023115906499, 360580025943812204, 360580028701968028, 360580031459926153, 360580032221995679, 360580032222282649, 360580030963116172, 360580029991888471, 360580030076059181, 360580032543414511]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 22180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 22100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360640404697540692, 360640407584735707⟩, ⟨(-1339889347822979345), (-1339845980072762235)⟩, true⟩

def words09 : List Nat := [360580033693633508, 360580034843779688, 360580038020109701, 360580042296804760, 360580045460296656, 360580048623550177, 360580050167011948, 360580051442904938, 360580054161882440, 360580056880710089]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 22190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 22100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 22100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk221B
