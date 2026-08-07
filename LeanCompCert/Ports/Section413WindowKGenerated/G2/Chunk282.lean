import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk282

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572218820972467, 360572223578603950⟩, ⟨285338372698204857, 285429116242306559⟩, true⟩

def state01 : KState := ⟨⟨360600102968997996, 360600107730138039⟩, ⟨(-501266607415862241), (-501175764913138187)⟩, true⟩

def words00 : List Nat := [360582345714794305, 360582345854696288, 360582345855034320, 360582344875739755, 360582343896451662, 360582342594740377, 360582342108486371, 360582342288573455, 360582342288904998, 360582342469604448]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360632969009767655, 360632973774416883⟩, ⟨(-1428593613593845521), (-1428502672079656769)⟩, true⟩

def words01 : List Nat := [360582344352344353, 360582346235059502, 360582349029934986, 360582350574116069, 360582350939381555, 360582351304643773, 360582351304950300, 360582351757638387, 360582353551774247, 360582355345867943]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360624899469070266, 360624904237263219⟩, ⟨(-1201223924018678553), (-1201132882482678931)⟩, true⟩

def words02 : List Nat := [360582356332850306, 360582356491997382, 360582356908008068, 360582357324107515, 360582357422743111, 360582357423117803, 360582357348720641, 360582356527498119, 360582356136149011, 360582357643714189]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360541638443576944, 360541643215280361⟩, ⟨1149648025280540152, 1149739165934776296⟩, true⟩

def words03 : List Nat := [360582358741196129, 360582359838666117, 360582360300800243, 360582360301173354, 360582360238892692, 360582359854682995, 360582359470392674, 360582358613112635, 360582357799899285, 360582356358550007]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580087044027125, 360580091819246744⟩, ⟨63798527968992733, 63889767937926349⟩, true⟩

def words04 : List Nat := [360582354917219067, 360582354210571319, 360582354946080791, 360582355744697041, 360582355745046362, 360582355348500151, 360582354307019798, 360582354077700112, 360582353848286772, 360582353403952512]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360528771006293517, 360528775785068285⟩, ⟨1513884624777728998, 1513975965197087830⟩, true⟩

def words05 : List Nat := [360582353324234552, 360582352479696367, 360582351635141127, 360582351891410458, 360582352138695339, 360582352386023441, 360582352386355597, 360582352007124884, 360582350786062164, 360582348890701587]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360563581577281179, 360563586359566416⟩, ⟨529887126323572144, 529978565966740862⟩, true⟩

def words06 : List Nat := [360582346995348311, 360582345920722169, 360582344493764723, 360582342440951216, 360582340388222278, 360582338015905431, 360582336598840824, 360582335750638172, 360582334902458107, 360582333390552152]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360608696747640684, 360608701533449932⟩, ⟨(-745988858271233394), (-745897318986944722)⟩, true⟩

def words07 : List Nat := [360582332727735910, 360582332485700525, 360582332243577456, 360582331926632536, 360582330806070364, 360582328614471676, 360582326422956791, 360582325478151731, 360582326097449673, 360582327030462522]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591770381087051, 360591775170446677⟩, ⟨(-267561826741699748), (-267470187034851446)⟩, true⟩

def words08 : List Nat := [360582327030797066, 360582327006106765, 360582326519217612, 360582326899112137, 360582326959557332, 360582326959930421, 360582325777175502, 360582323631509623, 360582321485921504, 360582320920436609]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575095219557545, 360575100012429469⟩, ⟨204404955134159009, 204496694221785591⟩, true⟩

def words09 : List Nat := [360582321788280089, 360582322656135363, 360582322899445418, 360582323584841690, 360582323951516513, 360582324318268180, 360582325929678286, 360582326298654091, 360582326298986622, 360582326044027412]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk282
