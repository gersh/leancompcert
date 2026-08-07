import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk863

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497489736128507, 362497602068974624⟩, ⟨(-1075627897885620949), (-1069082216606744961)⟩, true⟩

def state01 : KState := ⟨⟨362481738962832221, 362481851322830480⟩, ⟨283693343272473661, 290241367915220027⟩, true⟩

def words00 : List Nat := [371285214371797481, 371285214374798952, 371285214337967007, 371285214349917027, 371285214379625462, 371285214382647476, 371285214292085648, 371285214200258913, 371285214107244946, 371285214100815827]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 86300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 86300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362465189365169936, 362465301752194168⟩, ⟨1712252222131833136, 1718802579524808944⟩, true⟩

def words01 : List Nat := [371285214159016898, 371285214257425942, 371285214354937190, 371285214357939177, 371285214290871883, 371285214259018409, 371285214225696031, 371285214185061338, 371285213964840657, 371285213737591815]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 86310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 86300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481281177661635, 362481393591549259⟩, ⟨323146012288605156, 329698688666192770⟩, true⟩

def words02 : List Nat := [371285213508954832, 371285213385691191, 371285213194103010, 371285213137820183, 371285213080577158, 371285213003784438, 371285212788636960, 371285212699430301, 371285212639623998, 371285212642732697]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 86320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 86300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475178721383887, 362475291162620722⟩, ⟨850006342423866311, 856561379997510731⟩, true⟩

def words03 : List Nat := [371285212600778604, 371285212533977093, 371285212465993331, 371285212454636921, 371285212375050697, 371285212327619693, 371285212279146381, 371285212229742991, 371285212068141110, 371285211956922292]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 86330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 86300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475356277060755, 362475468745031615⟩, ⟨834684916663791893, 841242262589296105⟩, true⟩

def words04 : List Nat := [371285211863158443, 371285211866165669, 371285211742628515, 371285211603937816, 371285211464108384, 371285211332473300, 371285211154024077, 371285211098712390, 371285211042414783, 371285210983162354]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 86340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 86300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490063066617163, 362490175561786371⟩, ⟨(-435285335593035800), (-428725640955755204)⟩, true⟩

def words05 : List Nat := [371285210893538629, 371285210918397566, 371285211075571189, 371285211078574321, 371285211057341274, 371285211017373821, 371285211066979967, 371285211098147492, 371285211157715539, 371285211218611145]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487059563627753, 362487172085875959⟩, ⟨(-175940994772096045), (-169378961450460309)⟩, true⟩

def words06 : List Nat := [371285211251878178, 371285211254884263, 371285211142049846, 371285211144499136, 371285211160463542, 371285211163521966, 371285211088644541, 371285211014930755, 371285210996870280, 371285211023002420]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480098098856007, 362480210648161883⟩, ⟨425414864557022806, 431979234987313624⟩, true⟩

def words07 : List Nat := [371285211181669188, 371285211341565813, 371285211476292691, 371285211479303174, 371285211510736287, 371285211550045145, 371285211672699442, 371285211675703477, 371285211619935626, 371285211565445830]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484535425784812, 362484648001953032⟩, ⟨42130018134925473, 48696709073119801⟩, true⟩

def words08 : List Nat := [371285211585588507, 371285211597918400, 371285211677831668, 371285211758992067, 371285211828926248, 371285211831931549, 371285211747582303, 371285211683264202, 371285211683400942, 371285211686512277]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492043473258648, 362492156076886866⟩, ⟨(-606532781576240869), (-599963718243466157)⟩, true⟩

def words09 : List Nat := [371285211682256156, 371285211667483377, 371285211732113318, 371285211784842371, 371285211861732031, 371285211939743158, 371285212016600602, 371285212019619804, 371285212048557563, 371285212132739884]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk863
