import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk042

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362330393265159705, 362330393469414623⟩, ⟨632007748326466816, 632008329990137664⟩, true⟩

def state01 : KState := ⟨⟨362215819040447473, 362215819245712544⟩, ⟨1114911125287785445, 1114911711199487669⟩, true⟩

def words00 : List Nat := [371280856476383903, 371280856476498020, 371280828497623567, 371280801444782877, 371280774404767462, 371280758316510487, 371280714746758343, 371280693193082912, 371280671649610281, 371280643880201734]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 4200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 4200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362741645185966209, 362741645392259027⟩, ⟨(-1101595225904272736), (-1101594635660567700)⟩, true⟩

def words01 : List Nat := [371280580991503597, 371280574387090028, 371280588671159952, 371280588671275610, 371280567535245584, 371280538417025039, 371280536335153959, 371280542136387422, 371280604009274592, 371280665852893814]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 4210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 4200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362440656924197676, 362440657131522382⟩, ⟨168813720282277217, 168814314885724829⟩, true⟩

def words02 : List Nat := [371280712510071997, 371280712510185974, 371280694942055930, 371280705190849827, 371280726159558021, 371280726159672052, 371280672819665933, 371280618586678629, 371280565952877403, 371280565953008369]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 4220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 4200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362325185957333603, 362325186165687769⟩, ⟨658859877870931510, 658860476834316634⟩, true⟩

def words03 : List Nat := [371280602821709825, 371280649101061498, 371280689673017536, 371280689673131845, 371280675439204411, 371280654473688575, 371280649316915843, 371280649317030685, 371280614445066270, 371280577787582655]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 4230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 4200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362632221066249057, 362632221275630477⟩, ⟨(-643309472490278036), (-643308869166068956)⟩, true⟩

def words04 : List Nat := [371280560043594013, 371280560043722040, 371280611752258796, 371280665322717224, 371280711511242434, 371280711511357790, 371280750799806773, 371280791746094344, 371280854482766530, 371280890090223263]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 4240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 4200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362634251210423603, 362634251420850394⟩, ⟨(-651474025131294097), (-651473417358893137)⟩, true⟩

def words05 : List Nat := [371280926446698965, 371280962786114496, 371281054357929107, 371281119192607788, 371281185947378360, 371281252670833638, 371281306718971455, 371281306719086378, 371281323388466128, 371281359278780718]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 4250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 4200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495004535618071, 362495004747072307⟩, ⟨(-57386167778559076), (-57385555623936124)⟩, true⟩

def words06 : List Nat := [371281450262020098, 371281468045186624, 371281471476962513, 371281474907167379, 371281494179249614, 371281494179377531, 371281514171811785, 371281540390601597, 371281565506758218, 371281568653505476]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 4260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 4200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362700101978110708, 362700102190608535⟩, ⟨(-933368073731770979), (-933367457115684389)⟩, true⟩

def words07 : List Nat := [371281626582350179, 371281684484141287, 371281797116753727, 371281836958349714, 371281871158258236, 371281905342207640, 371281950556243911, 371281974717364092, 371282025681806284, 371282076622489945]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 4270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 4200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362586572828577181, 362586573042120157⟩, ⟨(-447892192124791545), (-447891571030205201)⟩, true⟩

def words08 : List Nat := [371282126564797412, 371282126564913063, 371282135969178747, 371282167891884009, 371282215724648585, 371282215724764297, 371282191215317980, 371282165843783313, 371282169412376160, 371282193743348262]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 4280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 4200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362561773389463640, 362561773604051782⟩, ⟨(-341125626445401833), (-341125000861622319)⟩, true⟩

def words09 : List Nat := [371282239679423631, 371282285594142884, 371282330589717366, 371282330589833754, 371282332507561884, 371282341432639539, 371282404434961075, 371282423754832733, 371282442208373299, 371282460653374818]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 4290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 4200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 4200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk042
