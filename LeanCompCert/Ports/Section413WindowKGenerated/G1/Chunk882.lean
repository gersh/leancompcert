import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk882

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486211351465550, 362486328882493132⟩, ⟨(-106715421103800268), (-99716178534360870)⟩, true⟩

def state01 : KState := ⟨⟨362471445629857860, 362471563188219835⟩, ⟨1195731033855777245, 1202732687463006533⟩, true⟩

def words00 : List Nat := [371285198463159134, 371285198466231923, 371285198431947101, 371285198398755256, 371285198364428332, 371285198326297445, 371285198226962678, 371285198182358230, 371285198136714179, 371285198067343098]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 88200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 88200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493265408304335, 362493382994411232⟩, ⟨(-729097839873307127), (-722093738743295087)⟩, true⟩

def words01 : List Nat := [371285197914855658, 371285197892290639, 371285197923356082, 371285197926483015, 371285197877168654, 371285197808379563, 371285197760810912, 371285197764249369, 371285197843165635, 371285197939393229]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 88210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 88200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485993293601201, 362486110907453188⟩, ⟨(-87567127963606184), (-80560579019032284)⟩, true⟩

def words02 : List Nat := [371285198009403061, 371285198012476621, 371285197935872124, 371285197964412681, 371285198029627530, 371285198032703546, 371285197952625115, 371285197873955770, 371285197829256504, 371285197843121842]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 88220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 88200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471268995790214, 362471386637329107⟩, ⟨1211653895207075679, 1218662887107516099⟩, true⟩

def words03 : List Nat := [371285197892756938, 371285197943647445, 371285197993542469, 371285197996616724, 371285197888469904, 371285197787514722, 371285197708597318, 371285197711671583, 371285197566494605, 371285197413474932]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 88230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 88200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474438230719988, 362474555899810975⟩, ⟨932062358997136716, 939073782235132884⟩, true⟩

def words04 : List Nat := [371285197259047411, 371285197234288917, 371285197230484562, 371285197289493664, 371285197319136686, 371285197322211390, 371285197180453962, 371285197090739993, 371285196999442503, 371285196962499192]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 88240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 88200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362471892257571350, 362472009954643537⟩, ⟨1156753533261828343, 1163767425984678247⟩, true⟩

def words05 : List Nat := [371285196844223300, 371285196716415051, 371285196587400088, 371285196512999304, 371285196373052086, 371285196262841468, 371285196151504419, 371285196047989021, 371285195772438480, 371285195626816489]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470374839519228, 362470492564010841⟩, ⟨1290684371423068090, 1297700684323913838⟩, true⟩

def words06 : List Nat := [371285195479507435, 371285195461420832, 371285195271586358, 371285195061044123, 371285194849267980, 371285194669202686, 371285194434009279, 371285194308286033, 371285194181554370, 371285194055846391]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484873310304314, 362484991062608642⟩, ⟨10848019160057218, 17866787230063422⟩, true⟩

def words07 : List Nat := [371285193891382467, 371285193842127630, 371285193836156568, 371285193839243761, 371285193783628337, 371285193689953383, 371285193595089396, 371285193554817989, 371285193449128957, 371285193450320809]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479663980565704, 362479781760656073⟩, ⟨470698025786580680, 477719246948935170⟩, true⟩

def words08 : List Nat := [371285193450355253, 371285193432434927, 371285193264632422, 371285193183780947, 371285193101378891, 371285193059159260, 371285192901096148, 371285192744205304, 371285192586018796, 371285192557427496]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470103122248974, 362470220930037507⟩, ⟨1314888999840609942, 1321912666615966748⟩, true⟩

def words09 : List Nat := [371285192498266195, 371285192493622596, 371285192487972448, 371285192478852067, 371285192310425990, 371285192182816606, 371285192053586055, 371285191962132876, 371285191794527277, 371285191628413679]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk882
