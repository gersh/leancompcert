import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk757

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480788605761391, 362480874170179742⟩, ⟨323938846686803362, 328312951523131592⟩, true⟩

def state01 : KState := ⟨⟨362494677185232891, 362494762772958831⟩, ⟨(-727486553193018306), (-723110683853663776)⟩, true⟩

def words00 : List Nat := [371285211164658883, 371285211167554539, 371285211285576917, 371285211433741942, 371285211535530984, 371285211538137820, 371285211448732246, 371285211493449798, 371285211711167585, 371285211840018391]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 75700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 75700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487507467261898, 362487593078801624⟩, ⟨(-184598459197634357), (-180220786797417897)⟩, true⟩

def words01 : List Nat := [371285211968122495, 371285212097205233, 371285212315363792, 371285212447444267, 371285212617754751, 371285212789036082, 371285212952412768, 371285212955027221, 371285212980635027, 371285213015321250]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 75710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 75700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481289086914505, 362481374721678494⟩, ⟨286311801318503468, 290691232382370748⟩, true⟩

def words02 : List Nat := [371285213222826641, 371285213225433942, 371285213200702011, 371285213166300278, 371285213130916139, 371285213124943238, 371285213114906827, 371285213178144879, 371285213240468488, 371285213243167764]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 75720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 75700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492237468557987, 362492323126893200⟩, ⟨(-542850921058040416), (-538469704824927838)⟩, true⟩

def words03 : List Nat := [371285213317824015, 371285213444486947, 371285213625911270, 371285213628524547, 371285213629894457, 371285213560856470, 371285213565881193, 371285213578801118, 371285213674441276, 371285213771262499]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 75730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 75700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486223340074849, 362486309021923083⟩, ⟨(-87352844741621464), (-82969847513309732)⟩, true⟩

def words04 : List Nat := [371285213867088882, 371285213869696913, 371285213768843467, 371285213807825251, 371285213898434238, 371285213901060169, 371285213839412365, 371285213743934752, 371285213707425799, 371285213724864123]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 75740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 75700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474016376045005, 362474102081389629⟩, ⟨837451926813966054, 841836704014049378⟩, true⟩

def words05 : List Nat := [371285213856289381, 371285213988795488, 371285214117411530, 371285214120066047, 371285214135580813, 371285214168891451, 371285214256160958, 371285214258769385, 371285214114010461, 371285213970302170]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481129206104136, 362481214934846184⟩, ⟨298571155744585298, 302957705646786368⟩, true⟩

def words06 : List Nat := [371285213825432165, 371285213742313191, 371285213594583716, 371285213602276963, 371285213604295427, 371285213584183888, 371285213359554905, 371285213310483219, 371285213318124789, 371285213320825421]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476273743965136, 362476359496455985⟩, ⟨666543479186926739, 670931828656255585⟩, true⟩

def words07 : List Nat := [371285213270024328, 371285213219169397, 371285213287678087, 371285213336767291, 371285213391748799, 371285213447733621, 371285213483442580, 371285213486051731, 371285213289507801, 371285213175905131]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482514989470957, 362482600765226044⟩, ⟨193573417132987170, 197963529687925118⟩, true⟩

def words08 : List Nat := [371285213118045014, 371285213120699750, 371285213035173368, 371285212950587395, 371285212864983274, 371285212805246862, 371285212714480849, 371285212758027024, 371285212763148172, 371285212765881645]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504388089916372, 362504473889265538⟩, ⟨(-1464305308766526698), (-1459913407894945060)⟩, true⟩

def words09 : List Nat := [371285212827083721, 371285212924131396, 371285213193772648, 371285213232265971, 371285213248221983, 371285213265014360, 371285213454683780, 371285213559097384, 371285213814961514, 371285214072008577]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk757
