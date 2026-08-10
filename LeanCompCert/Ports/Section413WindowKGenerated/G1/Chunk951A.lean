import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk951A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485820623173871, 362485958060363817⟩, ⟨(-80402275822684006), (-71577699661356334)⟩, true⟩

def state01 : KState := ⟨⟨362487248548335222, 362487386015252755⟩, ⟨(-216168012177840537), (-207340608769132203)⟩, true⟩

def words00 : List Nat := [371285205531927534, 371285205562080860, 371285205591723758, 371285205622517102, 371285205665344942, 371285205672813552, 371285205789509629, 371285205907551263, 371285206003298185, 371285206029669919]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 95100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 95100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362503213151698867, 362503350648779540⟩, ⟨(-1734628903753483625), (-1725798631378403501)⟩, true⟩

def words01 : List Nat := [371285206165510834, 371285206303145877, 371285206535523806, 371285206654592982, 371285206741909409, 371285206830289971, 371285206973518198, 371285207068553954, 371285207261558676, 371285207456094661]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 95110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 95100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489017613519847, 362489155140735247⟩, ⟨(-384325167786844512), (-375492028846042568)⟩, true⟩

def words02 : List Nat := [371285207648660371, 371285207704491882, 371285207795307267, 371285207887774591, 371285208011577150, 371285208014911256, 371285207991522807, 371285207959130808, 371285207990514521, 371285208035912991]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 95120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 95100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480584147192132, 362480721704379722⟩, ⟨418060796288968975, 426896786639510729⟩, true⟩

def words03 : List Nat := [371285208190274430, 371285208345970128, 371285208498472753, 371285208546222826, 371285208618808765, 371285208693091711, 371285208811281976, 371285208814616412, 371285208785735322, 371285208742288483]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 95130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 95100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488439821506839, 362488577408536306⟩, ⟨(-329326777278335873), (-320487947619163675)⟩, true⟩

def words04 : List Nat := [371285208748214862, 371285208751890223, 371285208860101824, 371285208972078556, 371285209066134773, 371285209069469760, 371285209057285416, 371285209088927398, 371285209165984925, 371285209204864047]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 95140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 95100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk951A
