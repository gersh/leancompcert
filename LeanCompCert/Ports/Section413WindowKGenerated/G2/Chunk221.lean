import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk221

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360646501982133384, 360646504842208790⟩, ⟨(-1472559978621590789), (-1472517211571310485)⟩, true⟩

def state01 : KState := ⟨⟨360660663435033504, 360660666297828478⟩, ⟨(-1786131504746138694), (-1786088677579846888)⟩, true⟩

def words00 : List Nat := [360579879952577596, 360579880617720155, 360579881636279968, 360579882654833270, 360579883149250733, 360579883713901920, 360579883714156601, 360579883248629733, 360579884358216332, 360579888012016898]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 22100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 22100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360555335966864365, 360555338832354197⟩, ⟨543461165339869370, 543504052102912078⟩, true⟩

def words01 : List Nat := [360579893706060883, 360579899399644442, 360579903434558286, 360579905436149123, 360579906914752236, 360579908393297656, 360579910538146463, 360579910650239693, 360579910650494523, 360579909539953787]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 22110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 22100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360644760819144405, 360644763687332703⟩, ⟨(-1435102206667255858), (-1435059260200600264)⟩, true⟩

def words02 : List Nat := [360579908429445522, 360579907819490554, 360579910072992490, 360579912326345298, 360579912715017158, 360579913788454113, 360579914148534705, 360579914508661991, 360579916906187133, 360579919836616486]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 22120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 22100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360619952464194344, 360619955335110820⟩, ⟨(-885772381457611614), (-885729374603312258)⟩, true⟩

def words03 : List Nat := [360579921748789613, 360579923660820760, 360579927609584545, 360579933339870444, 360579938056558088, 360579942772865773, 360579946243146549, 360579947684040393, 360579949491303450, 360579951298499858]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 22130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 22100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360564338994896275, 360564341868510516⟩, ⟨345517130422007989, 345560197018376321⟩, true⟩

def words04 : List Nat := [360579953032696745, 360579953032983096, 360579952738304368, 360579950759813160, 360579948781454135, 360579945809313902, 360579943948670414, 360579944036023580, 360579944036281382, 360579942780339789]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 22140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 22100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk221
