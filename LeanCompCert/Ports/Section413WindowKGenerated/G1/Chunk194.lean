import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk194

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362452245210741990, 362452250236260984⟩, ⟨646318029083637216, 646383969805191512⟩, true⟩

def state01 : KState := ⟨⟨362417223092595622, 362417228123531059⟩, ⟨1325805115777009892, 1325871161604851314⟩, true⟩

def words00 : List Nat := [371285567280666968, 371285565221728360, 371285560093096186, 371285557608481096, 371285555123809580, 371285553457803710, 371285548845550271, 371285544243634868, 371285539641944631, 371285536787189218]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 19400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 19400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362399285096757841, 362399290133098478⟩, ⟨1674053235253897154, 1674119386024819326⟩, true⟩

def words01 : List Nat := [371285533268534653, 371285530375242175, 371285527482054596, 371285524576698756, 371285518976154731, 371285513424841455, 371285507873785184, 371285504963116277, 371285500513295157, 371285496074706348]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 19410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 19400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362501594441262291, 362501599482980431⟩, ⟨(-313201906611503432), (-313135651381830716)⟩, true⟩

def words02 : List Nat := [371285491636314242, 371285489837084781, 371285487106185563, 371285487013991944, 371285486921621555, 371285485998278404, 371285482708770289, 371285482057429813, 371285483391190355, 371285484221214087]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 19420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 19400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472975702496347, 362472980749712366⟩, ⟨243186240631952439, 243252602712056305⟩, true⟩

def words03 : List Nat := [371285484680850222, 371285485140652723, 371285488236445847, 371285490221240803, 371285492304372527, 371285494387511845, 371285496146059086, 371285496146660795, 371285494386625314, 371285493743679036]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 19430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 19400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472459507808087, 362472464560382448⟩, ⟨253301444673109179, 253367910947457459⟩, true⟩

def words04 : List Nat := [371285495090553229, 371285495091155011, 371285493564566520, 371285492050299042, 371285490535963082, 371285489837229446, 371285489202619180, 371285490201555489, 371285491187571158, 371285491188194657]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 19440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 19400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362510357680583974, 362510362738599875⟩, ⟨(-483949693346589436), (-483883121206836560)⟩, true⟩

def words05 : List Nat := [371285492047432296, 371285493576531608, 371285496113464776, 371285496114066996, 371285495570862635, 371285494584958817, 371285495241781694, 371285495934422391, 371285497212676427, 371285498491068565]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 19450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 19400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469271106134636, 362469276169578631⟩, ⟨315649086530036157, 315715764328591945⟩, true⟩

def words06 : List Nat := [371285499743720219, 371285499744322964, 371285498882187374, 371285499765885938, 371285500759724357, 371285500760326896, 371285498245212338, 371285495177005238, 371285492108874034, 371285491668516926]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 19460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 19400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477199509765093, 362477204578638661⟩, ⟨161536397056444836, 161603180596872554⟩, true⟩

def words07 : List Nat := [371285492630416770, 371285494425186977, 371285496228837353, 371285496570829600, 371285497205397319, 371285497840195047, 371285501099931014, 371285501100534115, 371285500855003507, 371285500429798665]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 19470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 19400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485014661555947, 362485019735836526⟩, ⟨9263216848817706, 9330105744994592⟩, true⟩

def words08 : List Nat := [371285500004375486, 371285499636344958, 371285499437972885, 371285500651107594, 371285501446521180, 371285501447124523, 371285498739989355, 371285497768780038, 371285498447667106, 371285498448291375]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 19480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 19400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362451400754461060, 362451405834230489⟩, ⟨664777210177581694, 664844206079268158⟩, true⟩

def words09 : List Nat := [371285498424182014, 371285498375005575, 371285500501735301, 371285501660343856, 371285502869691503, 371285504079143503, 371285504866837762, 371285504867441453, 371285502156686934, 371285500408901221]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 19490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 19400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 19400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk194
