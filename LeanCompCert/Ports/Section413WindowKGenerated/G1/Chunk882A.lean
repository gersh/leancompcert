import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk882A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk882A
