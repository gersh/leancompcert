import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk567

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582354963745262, 360582375339049171⟩, ⟨(-34283220571721082), (-33502684602115914)⟩, true⟩

def state01 : KState := ⟨⟨360569443632758744, 360569464015492281⟩, ⟨697836784083018116, 698617741350686350⟩, true⟩

def words00 : List Nat := [360581784794950650, 360581784806878848, 360581784807582728, 360581784626515745, 360581784445330763, 360581784062414502, 360581783877699862, 360581783684786669, 360581783491800593, 360581783143359513]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 56700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 56700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360619078599842333, 360619098990033408⟩, ⟨(-2117183048604391820), (-2116401668382843992)⟩, true⟩

def words01 : List Nat := [360581783020154296, 360581783114406288, 360581783519011305, 360581783931522602, 360581784094168427, 360581784256873975, 360581784617748844, 360581785184233421, 360581785842734972, 360581786501389294]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 56710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 56700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587766204691967, 360587786602415624⟩, ⟨(-341091093686665040), (-340309286181509552)⟩, true⟩

def words02 : List Nat := [360581786890467885, 360581787058534572, 360581787468742717, 360581787879168946, 360581788208950419, 360581788302353835, 360581788303069811, 360581788156390752, 360581788009553862, 360581787954653704]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 56720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 56700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583211078350690, 360583231483512456⟩, ⟨(-82603405570723899), (-81821176062821507)⟩, true⟩

def words03 : List Nat := [360581788371398420, 360581788788283598, 360581789048999032, 360581789176381743, 360581789177054638, 360581789094102553, 360581789237402565, 360581789419633372, 360581789445752774, 360581789471985292]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 56730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 56700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360609558785387133, 360609579198021034⟩, ⟨(-1577615555688441398), (-1576832902175802052)⟩, true⟩

def words04 : List Nat := [360581789644139434, 360581790056097328, 360581790719581926, 360581791383194923, 360581791762623336, 360581792036879590, 360581792621158956, 360581793205649659, 360581793595401382, 360581794085826081]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 56740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 56700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360613251264246208, 360613271684408531⟩, ⟨(-1787259242992166167), (-1786476162204663313)⟩, true⟩

def words05 : List Nat := [360581794420192915, 360581794754634312, 360581795080008507, 360581795560599701, 360581795962132583, 360581796363794074, 360581796609480931, 360581796918291707, 360581797473454650, 360581798028866792]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 56750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 56700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360619116669737058, 360619137097347444⟩, ⟨(-2120300388395858779), (-2119516884818700939)⟩, true⟩

def words06 : List Nat := [360581798770651717, 360581799289627228, 360581799529272589, 360581799768975982, 360581799929824886, 360581800245657285, 360581800871179212, 360581801496830599, 360581801939128490, 360581802597606050]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 56760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 56700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360624059879165236, 360624080314237583⟩, ⟨(-2401053396270681733), (-2400269469041036105)⟩, true⟩

def words07 : List Nat := [360581803151386901, 360581803705382978, 360581804569012905, 360581805123670188, 360581805412699441, 360581805701779636, 360581805982468014, 360581806418044381, 360581807163204674, 360581807908520160]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 56770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 56700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360629109150061909, 360629129592673301⟩, ⟨(-2687853717251967344), (-2687069361918783858)⟩, true⟩

def words08 : List Nat := [360581808495839579, 360581809166605642, 360581810146989063, 360581811127589294, 360581811960387053, 360581812484296615, 360581812807889999, 360581813131557397, 360581813702311914, 360581814536380600]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 56780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 56700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575003840401946, 360575024290473083⟩, ⟨385028200489068375, 385812979498927533⟩, true⟩

def words09 : List Nat := [360581815235306928, 360581815934348008, 360581816399764251, 360581816642677825, 360581816734309550, 360581816826147400, 360581816854520521, 360581816890563135, 360581816891274564, 360581816772506515]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 56790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 56700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 56700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk567
