import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk665A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk665B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk665A

def state06 : KState := ⟨⟨360617598131753258, 360617626570894875⟩, ⟨(-2311758747988032814), (-2310480093516678154)⟩, true⟩

def words05 : List Nat := [360582910820252128, 360582911209726113, 360582911824206788, 360582912268658270, 360582912491293095, 360582912713998565, 360582912953248880, 360582913305836258, 360582913828128836, 360582914350622994]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601273592431958, 360601302040523496⟩, ⟨(-1225296523616155322), (-1224017273394300288)⟩, true⟩

def words06 : List Nat := [360582914700885615, 360582914949535802, 360582915126599601, 360582915303929922, 360582915424523795, 360582915425462908, 360582915377321085, 360582915216617939, 360582915119298806, 360582915396588535]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564787139674561, 360564815596605674⟩, ⟨1203889556771723635, 1205169395489173333⟩, true⟩

def words07 : List Nat := [360582915898724854, 360582916401034879, 360582916756907151, 360582916887830767, 360582916959207633, 360582917030832643, 360582917097339942, 360582917098279079, 360582916939833524, 360582916668932036]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593908154903640, 360593936620701407⟩, ⟨(-735121922625515808), (-733841493523230376)⟩, true⟩

def words08 : List Nat := [360582916397825966, 360582916343745276, 360582916412750486, 360582916481945951, 360582916482813421, 360582916343741887, 360582916182458364, 360582916215002540, 360582916323986170, 360582916490450725]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598206130410857, 360598234605176600⟩, ⟨(-1021351887651166150), (-1020070861328944100)⟩, true⟩

def words09 : List Nat := [360582916491310449, 360582916477789493, 360582916674645308, 360582917059013674, 360582917336640967, 360582917614411445, 360582917767309093, 360582917994051427, 360582918224794074, 360582918455849579]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk665B
