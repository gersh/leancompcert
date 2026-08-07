import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk646

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476060076823879, 362476121621732095⟩, ⟨605804053525300064, 608489409200571438⟩, true⟩

def state01 : KState := ⟨⟨362483227314849810, 362483288879464702⟩, ⟨142768723077052871, 145455351902527969⟩, true⟩

def words00 : List Nat := [371285540911852819, 371285540914298994, 371285540909685120, 371285540922157617, 371285540923859411, 371285540890951547, 371285540538165468, 371285540333378640, 371285540159476795, 371285540161803389]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 64600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 64600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484053692700916, 362484115277320334⟩, ⟨89424001420472532, 92111922839901442⟩, true⟩

def words01 : List Nat := [371285540128620465, 371285540096618478, 371285540268840393, 371285540394811443, 371285540592864298, 371285540791773341, 371285540922660899, 371285540924859700, 371285540736501973, 371285540717166201]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 64610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 64600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480219266483654, 362480280870681182⟩, ⟨337247903961895097, 339937090620266899⟩, true⟩

def words02 : List Nat := [371285540913941037, 371285540916140141, 371285540848747401, 371285540781683935, 371285540713722893, 371285540648772910, 371285540516030720, 371285540570969318, 371285540609862550, 371285540612142118]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 64620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 64600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362506185379839922, 362506247003987014⟩, ⟨(-1341095701352207371), (-1338405225257153445)⟩, true⟩

def words03 : List Nat := [371285540549055199, 371285540568481046, 371285540826082635, 371285540839252435, 371285540840955922, 371285540829737478, 371285541017975658, 371285541153284367, 371285541475102993, 371285541797921868]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 64630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 64600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482099802561459, 362482161446514929⟩, ⟨215882291106040373, 218574047590346429⟩, true⟩

def words04 : List Nat := [371285542104733834, 371285542106933405, 371285542296740699, 371285542501332064, 371285542715961576, 371285542718161305, 371285542614092924, 371285542466760824, 371285542326409811, 371285542328921586]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 64640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 64600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362464564543265753, 362464626207039730⟩, ⟨1349677191817535465, 1352370229798419245⟩, true⟩

def words05 : List Nat := [371285542377445516, 371285542479172505, 371285542558147145, 371285542560347040, 371285542320511379, 371285542141404983, 371285541961114076, 371285541901192455, 371285541625949485, 371285541304933303]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 64650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 64600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492521698171142, 362492583381627408⟩, ⟨(-458112973441871872), (-455418662703071454)⟩, true⟩

def words06 : List Nat := [371285540982968301, 371285540901079801, 371285540791006222, 371285540857187651, 371285540886921957, 371285540889162562, 371285540855069628, 371285540959434685, 371285541185707379, 371285541296879947]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 64660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 64600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491625142977959, 362491686846553139⟩, ⟨(-400131388927564714), (-397435777004497466)⟩, true⟩

def words07 : List Nat := [371285541406976792, 371285541517845746, 371285541726885683, 371285541817551406, 371285541958829566, 371285542100926531, 371285542241887034, 371285542244088309, 371285542196600191, 371285542294412565]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 64670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 64600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474540135042107, 362474601858189285⟩, ⟨705047152734757618, 707744030679396788⟩, true⟩

def words08 : List Nat := [371285542597939130, 371285542600140200, 371285542585384276, 371285542571306149, 371285542560252004, 371285542562677439, 371285542448819577, 371285542434956110, 371285542420309793, 371285542405888766]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 64680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 64600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494439056761756, 362494500799772260⟩, ⟨(-582293259864806019), (-579595096859811967)⟩, true⟩

def words09 : List Nat := [371285542238272181, 371285542194833543, 371285542343048440, 371285542345288245, 371285542341334963, 371285542300042531, 371285542413023451, 371285542464209490, 371285542604166345, 371285542745076664]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 64690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 64600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 64600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk646
