import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk477

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480426578474182, 362480459330317347⟩, ⟨228598409188750876, 229653910394671402⟩, true⟩

def state01 : KState := ⟨⟨362476108510490832, 362476141276454084⟩, ⟨434661968781479029, 435718143588760181⟩, true⟩

def words00 : List Nat := [371285274115322975, 371285274124255043, 371285274133986200, 371285274144265939, 371285274145401514, 371285274138661729, 371285273910924417, 371285273910383076, 371285273912481230, 371285273914131485]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 47700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 47700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362503065855854185, 362503098636198576⟩, ⟨(-851542751157564654), (-850485890154904624)⟩, true⟩

def words01 : List Nat := [371285273970565676, 371285274219282309, 371285274905273748, 371285275007001467, 371285275034956769, 371285275063389960, 371285275529298107, 371285275839653734, 371285276214239653, 371285276589507290]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 47710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 47700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482679299875139, 362482712094533259⟩, ⟨121356143015224633, 122413687141904063⟩, true⟩

def words02 : List Nat := [371285276965288071, 371285276966875368, 371285276943531640, 371285277078419572, 371285277265289641, 371285277266905002, 371285277095756792, 371285276923917907, 371285276804373261, 371285276806185091]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 47720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 47700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472082871011472, 362472115679980602⟩, ⟨627253890713261342, 628312117974152560⟩, true⟩

def words03 : List Nat := [371285277053468226, 371285277355101551, 371285277566650369, 371285277568239548, 371285277303474834, 371285277175039285, 371285277353103938, 371285277354691795, 371285277079076906, 371285276805200002]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 47730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 47700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480432025939983, 362480464849103108⟩, ⟨228747832839478323, 229806737794794975⟩, true⟩

def words04 : List Nat := [371285276692588228, 371285276694338208, 371285277092482569, 371285277511557642, 371285277862481790, 371285277864070052, 371285277630865017, 371285277509349336, 371285277554007694, 371285277555653785]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 47740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 47700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477395650503955, 362477428488146984⟩, ⟨373755107696874065, 374814704140961975⟩, true⟩

def words05 : List Nat := [371285277456062057, 371285277267761494, 371285277124778017, 371285277126574931, 371285277037487039, 371285277061820343, 371285277086777860, 371285277088366432, 371285276529546029, 371285276367211913]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 47750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 47700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472691097676717, 362472723949489916⟩, ⟨598483963857722432, 599544237142542202⟩, true⟩

def words06 : List Nat := [371285276222815065, 371285276224422078, 371285275988423832, 371285275698154957, 371285275407305753, 371285275172796923, 371285274772630651, 371285274712533893, 371285274651860111, 371285274592930204]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 47760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 47700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489263258647727, 362489296124802583⟩, ⟨(-193319659463173269), (-192258701003567123)⟩, true⟩

def words07 : List Nat := [371285274331286200, 371285274288970854, 371285274326464390, 371285274328053670, 371285273826666761, 371285273258427017, 371285272689543547, 371285272558277230, 371285272290864497, 371285272376848301]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 47770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 47700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467639086039195, 362467671966566053⟩, ⟨840001031139091467, 841062676365589745⟩, true⟩

def words08 : List Nat := [371285272461203042, 371285272462820081, 371285272289226661, 371285272397225675, 371285272604968642, 371285272606558223, 371285272231371769, 371285271794042306, 371285271356110615, 371285271101873975]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 47780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 47700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362458844504656617, 362458877399503296⟩, ⟨1260440143027085049, 1261502472671527617⟩, true⟩

def words09 : List Nat := [371285270803166932, 371285270873376977, 371285270928197411, 371285270929789484, 371285270515088721, 371285270117868654, 371285269757360556, 371285269758950513, 371285269214950206, 371285268664621948]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 47790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 47700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 47700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk477
