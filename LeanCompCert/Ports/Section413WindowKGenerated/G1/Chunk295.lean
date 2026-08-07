import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk295

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362465457325599876, 362465469367029959⟩, ⟨593274586315875100, 593514700767001742⟩, true⟩

def state01 : KState := ⟨⟨362498199730867003, 362498211780749423⟩, ⟨(-372658440373352965), (-372418076534795109)⟩, true⟩

def words00 : List Nat := [371285588293688984, 371285588353498306, 371285589412745966, 371285590472317827, 371285591277620851, 371285591278565313, 371285590670398049, 371285590787268403, 371285591716177547, 371285592144798937]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 29500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 29500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478406029280760, 362478418087797256⟩, ⟨211649834683103790, 211890453355594078⟩, true⟩

def words01 : List Nat := [371285592586810604, 371285593029132359, 371285594053698962, 371285594502710563, 371285595303641310, 371285596104870195, 371285596911143765, 371285596912088667, 371285596190650817, 371285595948683286]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 29510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 29500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478988934765243, 362479001001700779⟩, ⟨194504493527667545, 194745360773979671⟩, true⟩

def words02 : List Nat := [371285596412134832, 371285596413080649, 371285595889062040, 371285595350180702, 371285594810977587, 371285594615561138, 371285594704208163, 371285595321729523, 371285595831768021, 371285595832746292]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 29520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 29500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362519382038552365, 362519394114039684⟩, ⟨(-998526090687093159), (-998284970863887805)⟩, true⟩

def words03 : List Nat := [371285596531595029, 371285597454179654, 371285598854755041, 371285598855700620, 371285598730318556, 371285598274994157, 371285598507270845, 371285598622605681, 371285599767306741, 371285600912358499]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 29530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 29500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490132925573476, 362490145009588431⟩, ⟨(-134458266888646405), (-134216895115191461)⟩, true⟩

def words04 : List Nat := [371285601962371880, 371285601963317750, 371285601955134638, 371285602423310582, 371285603142113382, 371285603146634198, 371285603147361382, 371285602842553236, 371285602981601416, 371285603136382273]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 29540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 29500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362459223172172273, 362459235264709573⟩, ⟨779266678949533145, 779508302602974617⟩, true⟩

def words05 : List Nat := [371285604134456604, 371285605132858530, 371285606136505291, 371285606188705251, 371285606363360468, 371285606538469074, 371285607296100156, 371285607297046513, 371285606531361145, 371285605640305073]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 29550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 29500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362462031821262947, 362462043922294262⟩, ⟨696190557483907164, 696432432261938434⟩, true⟩

def words06 : List Nat := [371285604748893033, 371285604063881673, 371285602953720517, 371285602262245653, 371285601570537937, 371285600744052941, 371285598394690199, 371285597187805165, 371285595980472015, 371285595915268965]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 29560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 29500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463873145440746, 362463885255081711⟩, ⟨641826491049750925, 642068620458858409⟩, true⟩

def words07 : List Nat := [371285595119521745, 371285594329723528, 371285593890359253, 371285593891412879, 371285593773460195, 371285593673081110, 371285593572382239, 371285593477576560, 371285592161535620, 371285591428863282]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 29570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 29500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470657189144434, 362470669307233980⟩, ⟨441210213423595210, 441452592785969544⟩, true⟩

def words08 : List Nat := [371285591102826646, 371285591103790155, 371285590562242161, 371285589991640378, 371285589420703246, 371285589017423734, 371285588203114744, 371285588366987651, 371285588367708770, 371285588286375108]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 29580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 29500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362516408914130584, 362516421040791104⟩, ⟨(-912809404443958404), (-912566771424001136)⟩, true⟩

def words09 : List Nat := [371285588263330197, 371285588744934671, 371285590210419572, 371285590211367242, 371285590156985891, 371285589909203799, 371285590135942006, 371285590136985943, 371285591081218018, 371285592123814516]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 29590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 29500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 29500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk295
