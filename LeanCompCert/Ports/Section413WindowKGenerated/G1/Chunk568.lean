import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk568

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476662310231251, 362476709408107214⟩, ⟨464673348613265345, 466480471733344827⟩, true⟩

def state01 : KState := ⟨⟨362500123885400055, 362500171000403873⟩, ⟨(-868053392426230996), (-866245296356509730)⟩, true⟩

def words00 : List Nat := [371284922081534697, 371284922083643718, 371284922296747616, 371284922532689151, 371284922685501658, 371284922687415886, 371284922475347943, 371284922525962630, 371284922885461720, 371284923155860449]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 56800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 56800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492290960292707, 362492338092728357⟩, ⟨(-422958458447285090), (-421149371985281012)⟩, true⟩

def words01 : List Nat := [371284923407026462, 371284923658846719, 371284924219759717, 371284924652308619, 371284925098384863, 371284925545194945, 371284925962197726, 371284925966844663, 371284926098615707, 371284926231409738]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 56810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 56800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492910302975285, 362492957452466309⟩, ⟨(-458125836228847463), (-456315780591666103)⟩, true⟩

def words02 : List Nat := [371284926672957252, 371284926702351647, 371284926730327106, 371284926758956197, 371284926879343141, 371284926921157373, 371284927271826433, 371284927623244422, 371284927962879018, 371284928106148425]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 56820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 56800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500403162813709, 362500450329663968⟩, ⟨(-884010150161208487), (-882199107914364031)⟩, true⟩

def words03 : List Nat := [371284928441503093, 371284928777864050, 371284929187443341, 371284929219044455, 371284929220542083, 371284929202612592, 371284929322395973, 371284929324506652, 371284929583121735, 371284929858385941]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 56830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 56800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485423351956178, 362485470536086939⟩, ⟨(-32509869403547280), (-30697844845447374)⟩, true⟩

def words04 : List Nat := [371284930131921695, 371284930133837434, 371284930241892950, 371284930452347166, 371284930755554557, 371284930757470994, 371284930700123332, 371284930584114264, 371284930554218849, 371284930565904437]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 56840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 56800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362484698849034042, 362484746050373908⟩, ⟨8781008189857771, 10594011174158655⟩, true⟩

def words05 : List Nat := [371284930857147410, 371284931149141981, 371284931441791531, 371284931526748177, 371284931684928196, 371284931844069509, 371284932311617542, 371284932367541527, 371284932368983878, 371284932367840918]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482301887147964, 362482349105679226⟩, ⟨145122025079934256, 146936005653130836⟩, true⟩

def words06 : List Nat := [371284932490125538, 371284932499112874, 371284932764723839, 371284933031131282, 371284933198080871, 371284933199997217, 371284932954662638, 371284932863153743, 371284932821030714, 371284932823028499]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362479503895551795, 362479551131553564⟩, ⟨304299208982955318, 306114183191072690⟩, true⟩

def words07 : List Nat := [371284932779044021, 371284932718054166, 371284932902436628, 371284932996682793, 371284933094845613, 371284933193689911, 371284933290933809, 371284933292850530, 371284932978024053, 371284932885829076]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473921490467688, 362473968743561337⟩, ⟨621901238731267462, 623717185214388566⟩, true⟩

def words08 : List Nat := [371284932856137393, 371284932858092917, 371284932725172254, 371284932574676124, 371284932423470155, 371284932348045165, 371284932226623728, 371284932300832035, 371284932306091189, 371284932308075565]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505017236968598, 362505064507375741⟩, ⟨(-1147269796118294099), (-1145452864583617045)⟩, true⟩

def words09 : List Nat := [371284932232993451, 371284932351606403, 371284932778250789, 371284932793787284, 371284932795271185, 371284932763206349, 371284933005082215, 371284933168328522, 371284933523435067, 371284933879362462]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk568
