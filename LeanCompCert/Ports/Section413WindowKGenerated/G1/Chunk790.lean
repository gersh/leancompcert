import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk790

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479121944058454, 362479215438599536⟩, ⟨468725053947539889, 473712654164717643⟩, true⟩

def state01 : KState := ⟨⟨362479106425477145, 362479199944492863⟩, ⟨470008329178128815, 474997863013249935⟩, true⟩

def words00 : List Nat := [371285211727268018, 371285211728134662, 371285211808432173, 371285211926245826, 371285211998948176, 371285212001676900, 371285211860671947, 371285211823786627, 371285211811849051, 371285211814674021]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 79000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 79000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478439406434338, 362478532950296686⟩, ⟨522727147893960589, 527718644987858911⟩, true⟩

def words01 : List Nat := [371285211740643993, 371285211667041966, 371285211597771606, 371285211600793188, 371285211548187586, 371285211546004102, 371285211542814042, 371285211540316645, 371285211323571196, 371285211242437763]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 79010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 79000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467614533963413, 362467708102170617⟩, ⟨1378158493517203866, 1383151914468700208⟩, true⟩

def words02 : List Nat := [371285211193994258, 371285211196723399, 371285211019668713, 371285210810567268, 371285210600373478, 371285210422640439, 371285210163695614, 371285210011770990, 371285209858970063, 371285209708073043]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 79020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 79000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481492392160448, 362481585985064717⟩, ⟨281329586196845064, 286324959077879410⟩, true⟩

def words03 : List Nat := [371285209488471881, 371285209430254355, 371285209410439186, 371285209413169851, 371285209268473306, 371285209078351865, 371285208887181901, 371285208764035310, 371285208560144918, 371285208517441715]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 79030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 79000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478635131293029, 362478728748807245⟩, ⟨507132968334821031, 512130286512052795⟩, true⟩

def words04 : List Nat := [371285208473651205, 371285208430593191, 371285208173426182, 371285208077594413, 371285207980388374, 371285207933344271, 371285207742115759, 371285207551321918, 371285207359396070, 371285207310306449]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 79040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 79000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362467958977007635, 362468052619118455⟩, ⟨1351153920424379922, 1356153183085315696⟩, true⟩

def words05 : List Nat := [371285207230238982, 371285207193752803, 371285207156379977, 371285207117629477, 371285206927052527, 371285206763494274, 371285206598464983, 371285206516591201, 371285206301083939, 371285206087156469]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480318182178989, 362480411848700895⟩, ⟨374021610903136113, 379022803632404597⟩, true⟩

def words06 : List Nat := [371285205872043331, 371285205805869333, 371285205669176820, 371285205682799462, 371285205684969551, 371285205656565947, 371285205474276793, 371285205394712170, 371285205355468344, 371285205358295336]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476822848676145, 362476916540141733⟩, ⟨650470289678393732, 655473454829402228⟩, true⟩

def words07 : List Nat := [371285205299713643, 371285205242166913, 371285205266795856, 371285205287738430, 371285205354611026, 371285205422501922, 371285205483092302, 371285205485829125, 371285205380229124, 371285205278821923]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475226361349526, 362475320077134145⟩, ⟨776722611832929200, 781727700260251126⟩, true⟩

def words08 : List Nat := [371285205205055906, 371285205207786993, 371285205026039054, 371285204824839220, 371285204622614899, 371285204470805829, 371285204262296265, 371285204214640436, 371285204166028140, 371285204104195218]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485603613810982, 362485697354275391⟩, ⟨(-44065962237638211), (-39058921761446727)⟩, true⟩

def words09 : List Nat := [371285204000123407, 371285204022454106, 371285204109834384, 371285204112566211, 371285204006811564, 371285203875853718, 371285203743769702, 371285203689047688, 371285203559496812, 371285203568839538]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk790
