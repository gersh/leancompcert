import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk055

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362199349614788174, 362199349974490789⟩, ⟨1555436938691975033, 1555438279213188007⟩, true⟩

def state01 : KState := ⟨⟨362410591020450820, 362410591381516723⟩, ⟨393369271305381101, 393370619331529581⟩, true⟩

def words00 : List Nat := [371282105524351183, 371282086941690915, 371282059604171708, 371282062335762948, 371282062335880701, 371282059220009606, 371282012363285606, 371281998279032158, 371281984199815023, 371281983508437146]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 5500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 5500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362451470556104349, 362451470918560776⟩, ⟨167782211595731393, 167783567290679035⟩, true⟩

def words01 : List Nat := [371281970554074228, 371281950367848250, 371281933130293568, 371281933130461322, 371281919755721250, 371281916638163157, 371281913521683723, 371281910129540203, 371281871999596994, 371281866492345320]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 5510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 5500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362447972299609090, 362447972663428471⟩, ⟨187444806028058312, 187446169253708932⟩, true⟩

def words02 : List Nat := [371281888080601912, 371281888080755658, 371281886544762581, 371281878302543688, 371281870063252522, 371281863799426504, 371281851856317471, 371281862161743201, 371281868896405748, 371281868896566574]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 5520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 5500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362576052745480825, 362576053110681375⟩, ⟨(-521287649500025170), (-521286278629295010)⟩, true⟩

def words03 : List Nat := [371281889162626814, 371281915547632689, 371281958411079311, 371281958411232473, 371281957931470036, 371281950081388335, 371281947518901197, 371281947519070503, 371281958114368460, 371281975096129978]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 5530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 5500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479101093552723, 362479101460138306⟩, ⟨15883277225881269, 15884655776651543⟩, true⟩

def words04 : List Nat := [371281992019860471, 371281992020014300, 371281984354315411, 371281991602421647, 371282009100176365, 371282009100329992, 371281992017158965, 371281973908101580, 371281963560103296, 371281963560278244]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 5540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 5500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362280568534692134, 362280568902663739⟩, ⟨1118792837434141216, 1118794223684560296⟩, true⟩

def words05 : List Nat := [371281968837419064, 371281974628136096, 371281980248155606, 371281980248309321, 371281942878511815, 371281904386506802, 371281865908278202, 371281859621849953, 371281827082681369, 371281790885340819]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 5550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 5500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362541713907972743, 362541714277323194⟩, ⟨(-334090331988243205), (-334088938064500631)⟩, true⟩

def words06 : List Nat := [371281754700949491, 371281744170490905, 371281724261526913, 371281730371523197, 371281730371644401, 371281729156782894, 371281704656949754, 371281703826915127, 371281734216469958, 371281744983109498]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 5560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 5500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478123498176134, 362478123868932432⟩, ⟨21180752623464712, 21182154384918588⟩, true⟩

def words07 : List Nat := [371281755739583331, 371281766492249108, 371281809261970716, 371281836139098273, 371281870688327927, 371281905225228111, 371281934255768306, 371281934255922672, 371281920634181055, 371281919953947651]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 5570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 5500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467039616636622, 362467039988769082⟩, ⟨83285832791041953, 83287242238646055⟩, true⟩

def words08 : List Nat := [371281950522731680, 371281950522886113, 371281939178914180, 371281927727908478, 371281916280942777, 371281914860617988, 371281916840369237, 371281929277694582, 371281939316379196, 371281939316539860]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 5580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 5500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362532282359585743, 362532282733119841⟩, ⟨(-281586536838848136), (-281585119548964768)⟩, true⟩

def words09 : List Nat := [371281965771395627, 371281994880796170, 371282028094643905, 371282028094798680, 371282018903140545, 371282004172824058, 371281997953536331, 371281997953708146, 371281999675878671, 371282008653571731]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 5590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 5500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 5500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk055
