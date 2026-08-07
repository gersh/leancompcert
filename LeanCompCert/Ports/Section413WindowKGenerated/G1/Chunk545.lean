import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk545

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488999972532965, 362489043190078513⟩, ⟨(-226739906464415284), (-225148756757121708)⟩, true⟩

def state01 : KState := ⟨⟨362470699079345895, 362470742313427735⟩, ⟨770771298552190113, 772363349572099079⟩, true⟩

def words00 : List Nat := [371284912144150470, 371284912146018451, 371284912148194597, 371284912319026181, 371284912501599024, 371284912503430260, 371284912237713366, 371284911972921323, 371284911707439315, 371284911518152962]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 54500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 54500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362458292456459684, 362458335707050368⟩, ⟨1447189514514326360, 1448782465513327412⟩, true⟩

def words01 : List Nat := [371284911259465790, 371284911224692374, 371284911189293076, 371284911158115937, 371284910720129793, 371284910385911366, 371284910050724074, 371284910052263802, 371284909605183252, 371284909119844083]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 54510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 54500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362470995008901913, 362471038275921294⟩, ⟨754619460164171379, 756213306937022347⟩, true⟩

def words02 : List Nat := [371284908633689534, 371284908484446072, 371284908205026903, 371284908065917513, 371284907926261021, 371284907733148520, 371284907128968847, 371284906697225078, 371284906264522172, 371284906115769764]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 54520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 54500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481195408304207, 362481238692003988⟩, ⟨198331835426181738, 199926591864638614⟩, true⟩

def words03 : List Nat := [371284905862841944, 371284905617695261, 371284905371831340, 371284905366479908, 371284905205633944, 371284905106947793, 371284905007650270, 371284904846191304, 371284904444364046, 371284904379423582]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 54530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 54500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473986423905315, 362474029723928992⟩, ⟨591592620278550605, 593188267107659583⟩, true⟩

def words04 : List Nat := [371284904582082055, 371284904583914941, 371284904406126207, 371284904229343260, 371284904051806929, 371284903977735298, 371284903826442898, 371284903920031711, 371284903934075474, 371284903935974962]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 54540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 54500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362493389629183006, 362493432945819294⟩, ⟨(-467006473980324165), (-465409920850051125)⟩, true⟩

def words05 : List Nat := [371284903737900289, 371284903680280692, 371284903772291745, 371284903774124879, 371284903478571260, 371284903129923141, 371284902780556778, 371284902724876411, 371284902703233577, 371284902861677691]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475749075248233, 362475792408393698⟩, ⟨495487113460553920, 497084567417735526⟩, true⟩

def words06 : List Nat := [371284903011700331, 371284903013533671, 371284902752736084, 371284902791663519, 371284902845427186, 371284902847260665, 371284902453712656, 371284902039289460, 371284901624115923, 371284901526359939]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362460894203029794, 362460937552699842⟩, ⟨1306234184283559157, 1307832540071938245⟩, true⟩

def words07 : List Nat := [371284901360691075, 371284901307075815, 371284901252826594, 371284901199288143, 371284900824222589, 371284900477807981, 371284900130411398, 371284900118992289, 371284899743809895, 371284899306823550]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484804548096138, 362484847914171984⟩, ⟨1165431459931194, 2764682762277534⟩, true⟩

def words08 : List Nat := [371284898869055463, 371284898767430463, 371284898658971380, 371284898773785312, 371284898833860491, 371284898835727213, 371284898618621354, 371284898497650903, 371284898556763647, 371284898558662959]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473058998460299, 362473102381299741⟩, ⟨642416439576525489, 644016606083062645⟩, true⟩

def words09 : List Nat := [371284898559108102, 371284898555642748, 371284898584649308, 371284898586691632, 371284898453431804, 371284898394750255, 371284898335468906, 371284898276927034, 371284897770926470, 371284897557235329]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk545
