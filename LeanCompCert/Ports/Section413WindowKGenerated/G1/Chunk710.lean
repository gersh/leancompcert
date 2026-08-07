import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk710

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362507067052329450, 362507141947337575⟩, ⟨(-1556381446533871761), (-1552790230914610965)⟩, true⟩

def state01 : KState := ⟨⟨362485791057786251, 362485865974803386⟩, ⟨(-45736458542391226), (-42143680173035602)⟩, true⟩

def words00 : List Nat := [371285272237069563, 371285272263184784, 371285272378769390, 371285272495581397, 371285272618781431, 371285272621226105, 371285272555005641, 371285272490021376, 371285272482629383, 371285272493790965]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 71000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 71000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474597931511869, 362474672870385046⟩, ⟨749212974768019584, 752807305247802260⟩, true⟩

def words01 : List Nat := [371285272701800220, 371285272910772704, 371285273119287058, 371285273121720296, 371285273066036998, 371285273020321543, 371285273091967238, 371285273094400581, 371285272950823382, 371285272804280397]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 71010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 71000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478412651200608, 362478487611891235⟩, ⟨478345665187053844, 481941545252746950⟩, true⟩

def words02 : List Nat := [371285272656683382, 371285272621395086, 371285272636490037, 371285272744854651, 371285272818294878, 371285272820735326, 371285272690558919, 371285272656276806, 371285272651540566, 371285272654060076]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 71020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 71000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490160077069530, 362490235059960311⟩, ⟨(-356133323919623065), (-352535866868166503)⟩, true⟩

def words03 : List Nat := [371285272560357423, 371285272467871071, 371285272463569323, 371285272466251404, 371285272508244851, 371285272561146861, 371285272612823569, 371285272615274280, 371285272558779960, 371285272631688354]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 71030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 71000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476940171723059, 362477015176325819⟩, ⟨583073000469759006, 586672000053075558⟩, true⟩

def words04 : List Nat := [371285272849581103, 371285272852015425, 371285272806200655, 371285272714086498, 371285272621072869, 371285272568324291, 371285272415662948, 371285272406127817, 371285272395761192, 371285272347332900]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 71040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 71000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362493867157581876, 362493942184160859⟩, ⟨(-619674919194329192), (-616074358090009312)⟩, true⟩

def words05 : List Nat := [371285272292020021, 371285272354157778, 371285272566956847, 371285272569391570, 371285272518627863, 371285272437258231, 371285272354897136, 371285272356404213, 371285272404353749, 371285272529102670]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483157841695150, 362483232890221008⟩, ⟨141327985426491500, 144930106184478700⟩, true⟩

def words06 : List Nat := [371285272653333360, 371285272655768502, 371285272553546869, 371285272594028666, 371285272675264145, 371285272677699383, 371285272495328332, 371285272314195128, 371285272146003513, 371285272148785585]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362461158897321974, 362461233967823385⟩, ⟨1704908018963522030, 1708511701638273094⟩, true⟩

def words07 : List Nat := [371285272121793057, 371285272094563912, 371285272066496281, 371285272027097704, 371285271723323735, 371285271482755549, 371285271240963649, 371285271085730071, 371285270764986158, 371285270429579692]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477220422539503, 362477295514838708⟩, ⟨563221400864451103, 566826633039437691⟩, true⟩

def words08 : List Nat := [371285270093076129, 371285269955244806, 371285269747865755, 371285269706694968, 371285269664809375, 371285269578390429, 371285269227627360, 371285269046963226, 371285268878937138, 371285268881459041]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362469246710549659, 362469321825069604⟩, ⟨1130134970977546319, 1133741782935941657⟩, true⟩

def words09 : List Nat := [371285268771141975, 371285268660177168, 371285268548214206, 371285268496821207, 371285268368550989, 371285268274618943, 371285268179853832, 371285268083698206, 371285267781665985, 371285267560413289]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk710
