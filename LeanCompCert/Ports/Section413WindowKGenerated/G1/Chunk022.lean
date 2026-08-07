import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk022

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨361759090508142766, 361759090560455524⟩, ⟨1574981431233729911, 1574981509360097241⟩, true⟩

def state01 : KState := ⟨⟨362290865829756591, 362290865882567194⟩, ⟨402932902711422482, 402932981935567712⟩, true⟩

def words00 : List Nat := [371274665985009653, 371274495725104422, 371274223788082169, 371274154823170910, 371274085920797295, 371273966200684054, 371273576147589771, 371273388501408987, 371273201025091691, 371273188498827632]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 2200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 2200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362147019024813870, 362147019078133490⟩, ⟨722828748242003021, 722828828593697131⟩, true⟩

def words01 : List Nat := [371273106037261372, 371272971941828191, 371272905293790899, 371272905293852901, 371272918098295824, 371272956268011812, 371272994171734285, 371272994171790261, 371272764381622478, 371272617649572093]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 2210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 2200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362136793578918691, 362136793632739522⟩, ⟨747181408882721376, 747181490349731062⟩, true⟩

def words02 : List Nat := [371272523927918862, 371272523927975361, 371272403099918752, 371272277619835761, 371272152252522077, 371272075193503957, 371271930383951477, 371271904064917276, 371271877769479984, 371271852597021913]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 2220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 2200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362372680858238064, 362372680912571661⟩, ⟨218458315884289388, 218458398497334408⟩, true⟩

def words03 : List Nat := [371271702413750641, 371271672788577942, 371271643189910477, 371271608027005608, 371271309261069513, 371270970614601646, 371270632270879822, 371270490704032679, 371270250541134062, 371270206983329400]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 2230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 2200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362010130124834401, 362010130179681335⟩, ⟨1032213185065628223, 1032213268831184809⟩, true⟩

def words04 : List Nat := [371270163464376043, 371270120225617749, 371269887305303274, 371269850571206956, 371269837932730016, 371269837932786989, 371269600818592489, 371269322869116480, 371269045166793448, 371268891632495195]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 2240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 2200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361814753528211468, 361814753583571682⟩, ⟨1475424739210202373, 1475424824133302233⟩, true⟩

def words05 : List Nat := [371268687829134359, 371268678660111338, 371268669499209230, 371268660453338195, 371268517309808881, 371268358114746569, 371268199060722503, 371268171410432247, 371267885422433926, 371267596426108542]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 2250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 2200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362198415281434019, 362198415337309545⟩, ⟨605965809018801359, 605965895109124417⟩, true⟩

def words06 : List Nat := [371267307685395410, 371267032894548126, 371266699899599889, 371266518574848796, 371266337410189762, 371266120236314268, 371265738292060750, 371265548399765324, 371265360665491876, 371265360665551451]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 2260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 2200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362225833239050367, 362225833295452021⟩, ⟨544411074777845183, 544411162065157625⟩, true⟩

def words07 : List Nat := [371265243120315850, 371265125525702267, 371265081658794483, 371265081658857868, 371265060074928685, 371265041417549414, 371265022776539874, 371264958471244175, 371264714893478204, 371264610120919196]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 2270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 2200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362316942090789835, 362316942147709007⟩, ⟨337942598736996291, 337942687206955067⟩, true⟩

def words08 : List Nat := [371264590722158623, 371264590722217500, 371264523513147028, 371264456429652305, 371264389404852664, 371264380405050314, 371264371507235011, 371264461461123357, 371264515373503497, 371264515373563573]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 2280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 2200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362864845958026726, 362864846015471728⟩, ⟨(-918699779969040415), (-918699690292239425)⟩, true⟩

def words09 : List Nat := [371264516440502709, 371264581864684843, 371264835328731541, 371264899015805389, 371264913203980425, 371264927379820785, 371265129254752621, 371265237624634866, 371265411367453624, 371265584959282142]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 2290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 2200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 2200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk022
