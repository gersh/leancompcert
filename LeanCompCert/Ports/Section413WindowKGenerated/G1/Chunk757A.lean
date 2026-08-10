import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk757A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk757A
