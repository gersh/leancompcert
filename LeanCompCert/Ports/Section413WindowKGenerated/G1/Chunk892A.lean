import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk892A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476412680287889, 362476532995864307⟩, ⟨760718080449669501, 767964315655581279⟩, true⟩

def state01 : KState := ⟨⟨362492897800987764, 362493018144452742⟩, ⟨(-709847511334986978), (-702598788331978292)⟩, true⟩

def words00 : List Nat := [371285142366914596, 371285142326022906, 371285142239610858, 371285142261470567, 371285142270117390, 371285142273244045, 371285142200549813, 371285142216447112, 371285142356115535, 371285142447640332]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 89200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 89200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492090253108301, 362492210624839776⟩, ⟨(-637780666208004527), (-630529421406139455)⟩, true⟩

def words01 : List Nat := [371285142529884596, 371285142613149666, 371285142820685080, 371285142966843014, 371285143117744613, 371285143269852428, 371285143410082594, 371285143413195784, 371285143490092277, 371285143573120942]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 89210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 89200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487166326260436, 362487286725711465⟩, ⟨(-198422419496258961), (-191168701408867485)⟩, true⟩

def words02 : List Nat := [371285143718814826, 371285143761049182, 371285143802331484, 371285143844699099, 371285143914942560, 371285143923367902, 371285144055915365, 371285144189698527, 371285144296160784, 371285144323391545]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 89220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 89200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502648288249361, 362502768715866063⟩, ⟨(-1579966405856371020), (-1572710174410869860)⟩, true⟩

def words03 : List Nat := [371285144474977183, 371285144628259504, 371285144830642578, 371285144866692925, 371285144885372326, 371285144905025634, 371285145048834818, 371285145135618769, 371285145335213738, 371285145536224297]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 89230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 89200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481200860762948, 362481321316503204⟩, ⟨334049718122600476, 341308459452409690⟩, true⟩

def words04 : List Nat := [371285145735543452, 371285145768350520, 371285145795949955, 371285145825109895, 371285145874978749, 371285145878090428, 371285145760810719, 371285145639127171, 371285145516137051, 371285145500922839]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 89240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 89200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk892A
