import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk700

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360535467402754303, 360535498983749457⟩, ⟨3292658543057464593, 3294151772067183613⟩, true⟩

def state01 : KState := ⟨⟨360575503723251035, 360575535313601009⟩, ⟨489951699504369525, 491445583398070135⟩, true⟩

def words00 : List Nat := [360582557623314246, 360582557155701381, 360582556789789839, 360582556627611993, 360582556465358623, 360582556125995063, 360582555820165455, 360582555466381580, 360582555112316957, 360582554961985498]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 70000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 70000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580337577180962, 360580369176982659⟩, ⟨151480231593295256, 152974777248512400⟩, true⟩

def words01 : List Nat := [360582554862613142, 360582554659649382, 360582554456500400, 360582554489824446, 360582554490661923, 360582554417930647, 360582554345093416, 360582554170633836, 360582553936795175, 360582553906734852]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 70010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 70000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576424121233950, 360576455730383836⟩, ⟨425431567872396179, 426926768134034367⟩, true⟩

def words02 : List Nat := [360582553876349844, 360582553836055105, 360582553647878713, 360582553316099192, 360582552984168445, 360582552601182267, 360582552371532114, 360582552310990412, 360582552250333470, 360582552071496703]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 70020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 70000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595715336686022, 360595746955199731⟩, ⟨(-925680209002456557), (-924184352946600411)⟩, true⟩

def words03 : List Nat := [360582551985250413, 360582551959169575, 360582552043113576, 360582552101710526, 360582552102643502, 360582551953118417, 360582551803413127, 360582551686321759, 360582551860609913, 360582552050030665]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 70030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 70000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582911530429257, 360582943158401219⟩, ⟨(-28879416872137634), (-27382898312990216)⟩, true⟩

def words04 : List Nat := [360582552106866399, 360582552169581990, 360582552386265959, 360582552603239947, 360582552768854052, 360582552769846240, 360582552731984492, 360582552573861519, 360582552415560444, 360582552258937786]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 70040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 70000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360550460432927002, 360550492070245784⟩, ⟨2244575334593195164, 2246072507943540414⟩, true⟩

def words05 : List Nat := [360582552468551257, 360582552678348815, 360582552763326952, 360582552764319217, 360582552645740845, 360582552476412072, 360582552306773701, 360582552098862144, 360582551797560211, 360582551340984345]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 70050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 70000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360586598336852549, 360586629983550645⟩, ⟨(-287473484441583177), (-285975653931051509)⟩, true⟩

def words06 : List Nat := [360582550884195909, 360582550630894902, 360582550480087559, 360582550325266661, 360582550170381791, 360582549841181233, 360582549372373466, 360582549107019419, 360582548841382193, 360582548756596113]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 70060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 70000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591488933955662, 360591520590094385⟩, ⟨(-630188549493860062), (-628690057431247610)⟩, true⟩

def words07 : List Nat := [360582548757480456, 360582548715133377, 360582548782255483, 360582549042334860, 360582549250982372, 360582549459784736, 360582549500283748, 360582549501276834, 360582549555037622, 360582549684179355]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 70000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580294476742898, 360580326142223864⟩, ⟨154282796947742503, 155781943762311187⟩, true⟩

def words08 : List Nat := [360582549763958120, 360582549764950907, 360582549704673291, 360582549511925835, 360582549319004948, 360582549046590509, 360582548876500843, 360582548872079411, 360582548867550223, 360582548740936410]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 70080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 70000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592389583329255, 360592421258202962⟩, ⟨(-693671979233669444), (-692172174036902402)⟩, true⟩

def words09 : List Nat := [360582548710047638, 360582548534011674, 360582548357671372, 360582548293109211, 360582548086213292, 360582547705919823, 360582547325442486, 360582547109503816, 360582547189070662, 360582547330954608]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 70090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 70000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 70000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk700
