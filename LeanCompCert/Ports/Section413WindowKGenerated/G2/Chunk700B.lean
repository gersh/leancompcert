import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk700A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk700B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk700A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk700B
