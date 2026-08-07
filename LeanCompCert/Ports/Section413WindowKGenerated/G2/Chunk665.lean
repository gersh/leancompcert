import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk665

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574464705885638, 360574493091746823⟩, ⟨558746577705688630, 560021687432320802⟩, true⟩

def state01 : KState := ⟨⟨360577232423277150, 360577260818076921⟩, ⟨374545712657476758, 375821416844297216⟩, true⟩

def words00 : List Nat := [360582914344714199, 360582914101479976, 360582913728545849, 360582913523335417, 360582913317880105, 360582913025878852, 360582912699408289, 360582912197160597, 360582911694743952, 360582911418239969]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360558495559045473, 360558523962671826⟩, ⟨1620925890309065629, 1622202181596823539⟩, true⟩

def words01 : List Nat := [360582911432173816, 360582911531241711, 360582911532077596, 360582911518377246, 360582911510908699, 360582911409183913, 360582911307190619, 360582911240167881, 360582911011740438, 360582910646099319]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587393984615027, 360587422397116003⟩, ⟨(-301637415528165025), (-300360533857089583)⟩, true⟩

def words02 : List Nat := [360582910280276006, 360582909742114762, 360582909316860512, 360582909117269108, 360582908917611788, 360582908526568828, 360582908151023252, 360582907937018604, 360582907733077506, 360582907801906897]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583871620520249, 360583900041954334⟩, ⟨(-67253660730639686), (-65976184694569826)⟩, true⟩

def words03 : List Nat := [360582907802743166, 360582907731050291, 360582907811967412, 360582908110906661, 360582908253714566, 360582908396657571, 360582908425580931, 360582908498546218, 360582908514212741, 360582908530184229]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598108100745025, 360598136531030074⟩, ⟨(-1014590245312362902), (-1013312180288997788)⟩, true⟩

def words04 : List Nat := [360582908771221639, 360582909053143881, 360582909188952429, 360582909324858924, 360582909404074872, 360582909597089142, 360582909856898980, 360582910116877226, 360582910201270976, 360582910431042261]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk665
