import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk684

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489594837977920, 362489664146313023⟩, ⟨(-290758862605138891), (-287557087136987723)⟩, true⟩

def state01 : KState := ⟨⟨362485601798142224, 362485671127291664⟩, ⟨(-17575002553851082), (-14371803274947154)⟩, true⟩

def words00 : List Nat := [371285460409712160, 371285460432189106, 371285460446775891, 371285460462175196, 371285460541725857, 371285460544314430, 371285460720146032, 371285460900466731, 371285461041502137, 371285461046993541]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 68400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 68400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491667852418564, 362491737202719003⟩, ⟨(-432608130975744919), (-429403484649687351)⟩, true⟩

def words01 : List Nat := [371285461095119405, 371285461144401029, 371285461329296494, 371285461331635268, 371285461259556986, 371285461154194497, 371285461117217088, 371285461119865719, 371285461206459272, 371285461300808045]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 68410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 68400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362469684203984503, 362469753575332583⟩, ⟨1071581231977691828, 1074787318494486638⟩, true⟩

def words02 : List Nat := [371285461394543054, 371285461396881848, 371285461205917534, 371285461198443001, 371285461189829546, 371285461137143052, 371285460799385969, 371285460462155741, 371285460124005654, 371285459951461394]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 68420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 68400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362458687114103239, 362458756506566589⟩, ⟨1824204558813949827, 1827412090353715989⟩, true⟩

def words03 : List Nat := [371285459723537321, 371285459606740196, 371285459489068015, 371285459372288200, 371285458970394772, 371285458634698738, 371285458297800032, 371285458174846364, 371285457830502521, 371285457443012436]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 68430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 68400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489470839990551, 362489540253406726⟩, ⟨(-282754940449893552), (-279545974797239330)⟩, true⟩

def words04 : List Nat := [371285457054468578, 371285456854597527, 371285456594034582, 371285456547561322, 371285456500409346, 371285456434035934, 371285456189186004, 371285456158731973, 371285456306863818, 371285456368952193]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 68440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 68400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482995592700728, 362483065027433229⟩, ⟨160507722398883973, 163718147262816727⟩, true⟩

def words05 : List Nat := [371285456430638553, 371285456493092315, 371285456575328767, 371285456577930927, 371285456592728533, 371285456634365244, 371285456668817989, 371285456671169060, 371285456501852144, 371285456469841392]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470726320130083, 362470795775672946⟩, ⟨1000552458125930931, 1003764307777751337⟩, true⟩

def words06 : List Nat := [371285456587435191, 371285456589775391, 371285456458286570, 371285456327405059, 371285456195582914, 371285456129717316, 371285455956218483, 371285455873111511, 371285455789239336, 371285455689617415]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495519856381181, 362495589333119947⟩, ⟨(-697196450959567466), (-693983149922089598)⟩, true⟩

def words07 : List Nat := [371285455477110826, 371285455347240664, 371285455296366834, 371285455298748969, 371285455236119194, 371285455115700117, 371285455084342274, 371285455086921807, 371285455230719469, 371285455381368044]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490803712598861, 362490873210492802⟩, ⟨(-374272762798963501), (-371058012945920855)⟩, true⟩

def words08 : List Nat := [371285455491005351, 371285455493346530, 371285455401553992, 371285455464110944, 371285455590513960, 371285455592871105, 371285455535077359, 371285455457494228, 371285455511594633, 371285455593390615]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475313087699011, 362475382606640015⟩, ⟨686839966708150668, 690056158182345986⟩, true⟩

def words09 : List Nat := [371285455886954704, 371285456181441868, 371285456451847411, 371285456492350169, 371285456535174205, 371285456579153871, 371285456685540999, 371285456687884596, 371285456563621810, 371285456419168225]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk684
