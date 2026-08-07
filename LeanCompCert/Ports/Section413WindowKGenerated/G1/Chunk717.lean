import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk717

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484361285777189, 362484437723312480⟩, ⟨54441244348775396, 58142520390396170⟩, true⟩

def state01 : KState := ⟨⟨362474057891066081, 362474134350529680⟩, ⟨793242056288415198, 796944904701916496⟩, true⟩

def words00 : List Nat := [371285248697434222, 371285248699893228, 371285248512576484, 371285248326527749, 371285248139520668, 371285248012540133, 371285247826984378, 371285247833210451, 371285247835062905, 371285247792235188]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 71700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 71700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501209391659017, 362501285873371849⟩, ⟨(-1153916516961668199), (-1150212072945273179)⟩, true⟩

def words01 : List Nat := [371285247678194292, 371285247720469358, 371285247955633345, 371285247982292298, 371285247984229232, 371285247967851855, 371285248077281820, 371285248109407068, 371285248334692119, 371285248561107028]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 71710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 71700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487016418327195, 362487092922267121⟩, ⟨(-135925014930784673), (-132218976672227515)⟩, true⟩

def words02 : List Nat := [371285248783599614, 371285248877960250, 371285249095156382, 371285249313591491, 371285249567630542, 371285249570090791, 371285249565308691, 371285249561833351, 371285249632432277, 371285249660962076]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 71720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 71700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479130541677543, 362479207067746087⟩, ⟨429821448016069921, 433529073671885555⟩, true⟩

def words03 : List Nat := [371285249788588589, 371285249917179326, 371285250045418264, 371285250047892598, 371285250066967254, 371285250108192953, 371285250286446177, 371285250288906775, 371285250208527164, 371285250127038977]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 71730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 71700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490897689966012, 362490974238101595⟩, ⟨(-414392573681784554), (-410683364826121414)⟩, true⟩

def words04 : List Nat := [371285250154284441, 371285250199077697, 371285250294067035, 371285250390066573, 371285250453559145, 371285250456022324, 371285250308147167, 371285250289750513, 371285250425542675, 371285250507912105]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 71740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 71700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483142058165575, 362483218628732164⟩, ⟨142133984913933209, 145844803304132657⟩, true⟩

def words05 : List Nat := [371285250590005833, 371285250672950097, 371285250847739744, 371285250926246930, 371285251057234765, 371285251189139134, 371285251248227484, 371285251250688708, 371285251050877065, 371285251025656693]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479112681336959, 362479189273815742⟩, ⟨431335882211164051, 435048273134902969⟩, true⟩

def words06 : List Nat := [371285251164616319, 371285251167078253, 371285251105016420, 371285251036770262, 371285250967542641, 371285250950433767, 371285250882182244, 371285250931142753, 371285250972161237, 371285250974709360]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496988425709794, 362497065040444049⟩, ⟨(-851733274337385902), (-848019286024854924)⟩, true⟩

def words07 : List Nat := [371285250891949513, 371285250891584938, 371285251014876832, 371285251017345347, 371285250945040946, 371285250811907528, 371285250735768041, 371285250738528192, 371285250893286009, 371285251060616172]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494768055844565, 362494844692776532⟩, ⟨(-692401586618699536), (-688686004839963824)⟩, true⟩

def words08 : List Nat := [371285251217278962, 371285251219746454, 371285251266968778, 371285251361893655, 371285251469238609, 371285251471729466, 371285251462017694, 371285251453559087, 371285251626799619, 371285251763233275]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468903919343180, 362468980578497806⟩, ⟨1164568111991102984, 1168285289246812486⟩, true⟩

def words09 : List Nat := [371285251967929215, 371285252173695512, 371285252376755498, 371285252379218164, 371285252323726828, 371285252320830080, 371285252377965094, 371285252380427975, 371285252185187846, 371285251961356397]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk717
