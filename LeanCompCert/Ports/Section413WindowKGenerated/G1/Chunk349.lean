import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk349

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473990284966490, 362474007376358391⟩, ⟨381150708783568105, 381553843621334671⟩, true⟩

def state01 : KState := ⟨⟨362473365311631071, 362473382413170902⟩, ⟨403052554744508213, 403456043797819385⟩, true⟩

def words00 : List Nat := [371284940035925335, 371284940037206151, 371284940115324104, 371284940279463874, 371284940370928158, 371284940372062002, 371284939541252246, 371284939397508790, 371284939445621753, 371284939446794444]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 34900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 34900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362511406013486880, 362511423125377321⟩, ⟨(-925147133861517032), (-924743283418388304)⟩, true⟩

def words01 : List Nat := [371284939116607750, 371284938781314659, 371284938929490650, 371284939173474451, 371284939669253334, 371284940165449423, 371284940659027479, 371284940660169420, 371284941357530921, 371284942117289970]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 34910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 34900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362499998266856263, 362500015388849735⟩, ⟨(-526710197570343154), (-526305994276350388)⟩, true⟩

def words02 : List Nat := [371284943564207951, 371284944168129686, 371284944618116100, 371284945068433961, 371284945545000059, 371284945614252032, 371284946388129260, 371284947162437777, 371284947938635849, 371284948371178431]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 34920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 34900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362519878028928936, 362519895161151191⟩, ⟨(-1221205144048576793), (-1220800583410614005)⟩, true⟩

def words03 : List Nat := [371284949340759123, 371284950310854982, 371284952035953306, 371284952669535441, 371284953073251438, 371284953477312918, 371284954063217944, 371284954245428866, 371284955246224863, 371284956247456374]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 34930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 34900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491581793759039, 362491598936216867⟩, ⟨(-232491111561256628), (-232086193242262374)⟩, true⟩

def words04 : List Nat := [371284957220453450, 371284957221587706, 371284957709038211, 371284958316312334, 371284959061209989, 371284959062344457, 371284958825542814, 371284958416122675, 371284958414371923, 371284958605661454]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 34940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 34900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474917166592475, 362474934319292353⟩, ⟨350040589061455433, 350445865391543943⟩, true⟩

def words05 : List Nat := [371284959133609397, 371284959661987640, 371284960154538679, 371284960155673208, 371284959557555726, 371284959212142922, 371284959056789676, 371284959057951738, 371284958799974564, 371284958514526665]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 34950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 34900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491282578536913, 362491299741382614⟩, ⟨(-222027549968849087), (-221621918888890769)⟩, true⟩

def words06 : List Nat := [371284958759926868, 371284958885748486, 371284959829123852, 371284960772895726, 371284961459773464, 371284961460908371, 371284961386713416, 371284961717032599, 371284962253245345, 371284962435646751]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 34960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 34900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478477671711702, 362478494844899331⟩, ⟨225942944771873697, 226348937560885529⟩, true⟩

def words07 : List Nat := [371284962614851124, 371284962794438756, 371284963584633600, 371284964078172760, 371284964803935111, 371284965530104701, 371284966228365433, 371284966229500673, 371284965838596592, 371284965655006847]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 34970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 34900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470454598025139, 362470471781313628⟩, ⟨506681705424252540, 507088051594251374⟩, true⟩

def words08 : List Nat := [371284966102932157, 371284966104067677, 371284965648159412, 371284965126888759, 371284964605203860, 371284964335903793, 371284963926063258, 371284964042780905, 371284964150861173, 371284964152036528]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 34980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 34900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492990413479372, 362493007607063257⟩, ⟨(-282031463139816316), (-281624756683788498)⟩, true⟩

def words09 : List Nat := [371284963738638347, 371284963739798758, 371284964076856456, 371284964077992230, 371284963327318126, 371284962443481523, 371284961559238842, 371284961411618922, 371284961184134337, 371284961415334913]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 34990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 34900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 34900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk349
