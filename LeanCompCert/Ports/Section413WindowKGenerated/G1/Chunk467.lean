import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk467

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487226513444609, 362487257851915973⟩, ⟨(-88567756292379404), (-87578969064982254)⟩, true⟩

def state01 : KState := ⟨⟨362483619232379963, 362483650584861329⟩, ⟨79872534272119149, 80861975837144639⟩, true⟩

def words00 : List Nat := [371285382579609905, 371285382581164099, 371285382168789002, 371285382192817078, 371285382355951348, 371285382357512802, 371285382125222851, 371285381894127993, 371285381732204127, 371285381733990791]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 46700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 46700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362461672890252760, 362461704256724641⟩, ⟨1105132053084452248, 1106122148217783464⟩, true⟩

def words01 : List Nat := [371285381851886795, 371285382007462099, 371285382133054948, 371285382134606041, 371285381649917350, 371285381306007318, 371285380961329675, 371285380792815644, 371285380321404164, 371285379816403960]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 46710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 46700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486373404596447, 362486404784951466⟩, ⟨(-48942679137334805), (-47951935314070379)⟩, true⟩

def words02 : List Nat := [371285379310715904, 371285379144583884, 371285378925438624, 371285379045598725, 371285379046822243, 371285379044324740, 371285378498041419, 371285378409758077, 371285378634504919, 371285378658069652]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 46720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 46700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362464213584586639, 362464244979081836⟩, ⟨986781622843543021, 987773027508090341⟩, true⟩

def words03 : List Nat := [371285378659230890, 371285378636047777, 371285378878954903, 371285378918250599, 371285379041876791, 371285379166108224, 371285379279444023, 371285379280996049, 371285378784646721, 371285378334398655]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 46730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 46700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468098158126548, 362468129566453622⟩, ⟨805177096646958124, 806169147883033194⟩, true⟩

def words04 : List Nat := [371285377883315221, 371285377812216581, 371285377131249611, 371285376451558901, 371285375771290369, 371285375231453822, 371285374537085162, 371285374300083770, 371285374062572738, 371285373826301388]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 46740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 46700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489301171393845, 362489332593771686⟩, ⟨(-186142079967270043), (-185149371786294525)⟩, true⟩

def words05 : List Nat := [371285373546301437, 371285373635976413, 371285373915554053, 371285373917106735, 371285373640012805, 371285373294242519, 371285373056994961, 371285373058705514, 371285373024580282, 371285373111044921]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 46750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 46700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469041281972594, 362469072718352361⟩, ⟨761236348426447093, 762229711408850551⟩, true⟩

def words06 : List Nat := [371285373129739546, 371285373131292535, 371285372596162736, 371285372455286983, 371285372313649536, 371285372294452260, 371285371734044085, 371285371045764737, 371285370356863019, 371285370125053427]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 46760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 46700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478638644015081, 362478670094360908⟩, ⟨312424925435214926, 313418941683841282⟩, true⟩

def words07 : List Nat := [371285369885538632, 371285369995098248, 371285370102689397, 371285370104277244, 371285369947331079, 371285369928642144, 371285370232228275, 371285370233785140, 371285370084971240, 371285369943477707]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 46770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 46700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470035761501387, 362470067225778968⟩, ⟨714922870827091548, 715917538873542520⟩, true⟩

def words08 : List Nat := [371285369801333740, 371285369739597272, 371285369501196404, 371285369500054164, 371285369498402018, 371285369422424334, 371285368786246504, 371285368349956244, 371285367912866142, 371285367878458463]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 46780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 46700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471716440774688, 362471747919237438⟩, ⟨636320587976254362, 637315919814626862⟩, true⟩

def words09 : List Nat := [371285367552632677, 371285367228703243, 371285366985167938, 371285366986891649, 371285366914619531, 371285366865988962, 371285366816853325, 371285366747585381, 371285366069783167, 371285365780771939]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 46790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 46700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 46700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk467
