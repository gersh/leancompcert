import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk710A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk710A
