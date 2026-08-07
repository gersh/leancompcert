import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk265

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362459829758850080, 362459839388583166⟩, ⟨674161120490666288, 674333637313019422⟩, true⟩

def state01 : KState := ⟨⟨362491648650604302, 362491658287869976⟩, ⟨(-169038318776937009), (-168865602302323185)⟩, true⟩

def words00 : List Nat := [371285285442985219, 371285285443927024, 371285286238597059, 371285287084167895, 371285287892621698, 371285287893463225, 371285287401490447, 371285287622896692, 371285288403844181, 371285288644993347]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 26500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 26500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498923293638626, 362498932938573550⟩, ⟨(-361825954753845860), (-361653034929591508)⟩, true⟩

def words01 : List Nat := [371285288883684156, 371285289122650558, 371285290781583463, 371285291745612410, 371285293141120722, 371285294536852631, 371285295930304369, 371285295931145503, 371285295945250615, 371285296460502226]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 26510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 26500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362466870035507138, 362466879687942442⟩, ⟨488371912198085691, 488545030971796865⟩, true⟩

def words02 : List Nat := [371285297711938924, 371285297712780245, 371285297271099167, 371285296534232287, 371285295797106286, 371285295488768738, 371285294533870922, 371285294596723192, 371285294597353225, 371285294502528639]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 26520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 26500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485879379692960, 362485889039722396⟩, ⟨(-16025387596721553), (-15852067312208675)⟩, true⟩

def words03 : List Nat := [371285294275043235, 371285294742050444, 371285296077455998, 371285296078297643, 371285295522765253, 371285294665104788, 371285293807171229, 371285293120823759, 371285291749135361, 371285291772576765]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 26530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 26500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362456392697868940, 362456402365506702⟩, ⟨766546248416733756, 766719770664090572⟩, true⟩

def words04 : List Nat := [371285291776066425, 371285291776909581, 371285290262145745, 371285289174761305, 371285288087015530, 371285287431326844, 371285285429401229, 371285283426219067, 371285281422854217, 371285280699618344]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 26540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 26500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362461615307977592, 362461624983216387⟩, ⟨627920247030283703, 628093971123913251⟩, true⟩

def words05 : List Nat := [371285279612545128, 371285279115181730, 371285278617565469, 371285278052250055, 371285276607757772, 371285275530237578, 371285274789333459, 371285274790190670, 371285273989040486, 371285273099599065]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 26550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 26500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362499006977295559, 362499016660073446⟩, ⟨(-365258619466460228), (-365084695097060452)⟩, true⟩

def words06 : List Nat := [371285272734570503, 371285272735500542, 371285273849285495, 371285274993154980, 371285275560662677, 371285275561506088, 371285274634715960, 371285274757544206, 371285276173875644, 371285276691871382]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 26560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 26500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497581164735631, 362497590855197888⟩, ⟨(-327256876187329311), (-327082747605290625)⟩, true⟩

def words07 : List Nat := [371285277028168220, 371285277364733875, 371285279114741896, 371285280242548139, 371285281799346850, 371285283356366629, 371285284919040366, 371285284919883871, 371285285257941178, 371285285721922041]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 26570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 26500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362463571816092441, 362463581514068833⟩, ⟨576932870060157093, 577107198407542417⟩, true⟩

def words08 : List Nat := [371285287202303079, 371285287203146689, 371285286799338018, 371285286394160650, 371285285988687284, 371285285836547468, 371285285267861962, 371285285350773948, 371285285431902299, 371285285432775398]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 26580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 26500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362514761707550250, 362514771413178870⟩, ⟨(-784520944235183627), (-784346412378046051)⟩, true⟩

def words09 : List Nat := [371285285212636099, 371285285809112508, 371285286699773791, 371285286700617672, 371285285708839165, 371285284552184432, 371285283649033471, 371285283649974459, 371285284704972069, 371285285814427769]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 26590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 26500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 26500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk265
