import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk282A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk282A
