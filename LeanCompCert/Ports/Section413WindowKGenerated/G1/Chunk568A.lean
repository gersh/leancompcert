import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk568A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476662310231251, 362476709408107214⟩, ⟨464673348613265345, 466480471733344827⟩, true⟩

def state01 : KState := ⟨⟨362500123885400055, 362500171000403873⟩, ⟨(-868053392426230996), (-866245296356509730)⟩, true⟩

def words00 : List Nat := [371284922081534697, 371284922083643718, 371284922296747616, 371284922532689151, 371284922685501658, 371284922687415886, 371284922475347943, 371284922525962630, 371284922885461720, 371284923155860449]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 56800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 56800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492290960292707, 362492338092728357⟩, ⟨(-422958458447285090), (-421149371985281012)⟩, true⟩

def words01 : List Nat := [371284923407026462, 371284923658846719, 371284924219759717, 371284924652308619, 371284925098384863, 371284925545194945, 371284925962197726, 371284925966844663, 371284926098615707, 371284926231409738]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 56810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 56800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492910302975285, 362492957452466309⟩, ⟨(-458125836228847463), (-456315780591666103)⟩, true⟩

def words02 : List Nat := [371284926672957252, 371284926702351647, 371284926730327106, 371284926758956197, 371284926879343141, 371284926921157373, 371284927271826433, 371284927623244422, 371284927962879018, 371284928106148425]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 56820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 56800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500403162813709, 362500450329663968⟩, ⟨(-884010150161208487), (-882199107914364031)⟩, true⟩

def words03 : List Nat := [371284928441503093, 371284928777864050, 371284929187443341, 371284929219044455, 371284929220542083, 371284929202612592, 371284929322395973, 371284929324506652, 371284929583121735, 371284929858385941]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 56830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 56800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485423351956178, 362485470536086939⟩, ⟨(-32509869403547280), (-30697844845447374)⟩, true⟩

def words04 : List Nat := [371284930131921695, 371284930133837434, 371284930241892950, 371284930452347166, 371284930755554557, 371284930757470994, 371284930700123332, 371284930584114264, 371284930554218849, 371284930565904437]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 56840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 56800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk568A
