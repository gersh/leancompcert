import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk704A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489092325634048, 362489165911611272⟩, ⟨(-274869010972946986), (-271370344532691958)⟩, true⟩

def state01 : KState := ⟨⟨362484888088153886, 362484961695845141⟩, ⟨21068119389701358, 24568314612303022⟩, true⟩

def words00 : List Nat := [371285311333175020, 371285311335585927, 371285311125930270, 371285311062338240, 371285310997582038, 371285310995065425, 371285310856404023, 371285310718255117, 371285310625272258, 371285310628022564]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 70400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 70400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475596960819501, 362475670590239534⟩, ⟨675332423229366969, 678834148483986839⟩, true⟩

def words01 : List Nat := [371285310684893154, 371285310747667470, 371285310774027446, 371285310776450839, 371285310655588379, 371285310597492705, 371285310649426273, 371285310651838008, 371285310516339063, 371285310382180517]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 70410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 70400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487764431705683, 362487838082678564⟩, ⟨(-181520108366138980), (-178016865246859862)⟩, true⟩

def words02 : List Nat := [371285310246936135, 371285310245767473, 371285310301049321, 371285310431123659, 371285310529686169, 371285310532101521, 371285310412789105, 371285310379025675, 371285310508617918, 371285310547001847]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 70420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 70400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488460001688161, 362488533674670574⟩, ⟨(-230523461198638129), (-227018667839012657)⟩, true⟩

def words03 : List Nat := [371285310557551794, 371285310568947686, 371285310640657648, 371285310663361400, 371285310746490743, 371285310830520030, 371285310911458779, 371285310913872079, 371285310805847805, 371285310854610680]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 70430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 70400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468944424305969, 362469018118811972⟩, ⟨1144241732569837703, 1147748042161096123⟩, true⟩

def words04 : List Nat := [371285310941655867, 371285310944068247, 371285310762882952, 371285310581232711, 371285310398667988, 371285310274668273, 371285310056662392, 371285309972707575, 371285309887856424, 371285309787259965]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 70440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 70400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk704A
