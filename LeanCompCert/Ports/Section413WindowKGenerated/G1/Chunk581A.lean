import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk581A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488045040022643, 362488094407223043⟩, ⟨(-182686385071917999), (-180748883069585007)⟩, true⟩

def state01 : KState := ⟨⟨362488726104601371, 362488775489495279⟩, ⟨(-222296219561399499), (-220357689477035069)⟩, true⟩

def words00 : List Nat := [371284983516814061, 371284983518793352, 371284983465716915, 371284983561439057, 371284983745470184, 371284983747437404, 371284983630070308, 371284983458384975, 371284983408612144, 371284983476116108]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 58100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 58100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483660385015273, 362483709787575157⟩, ⟨72182940611325325, 74122497356601965⟩, true⟩

def words01 : List Nat := [371284983839165781, 371284984203028597, 371284984500501900, 371284984555323130, 371284984669262550, 371284984784147696, 371284985159812684, 371284985161775176, 371284985142764253, 371284985123042408]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 58110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 58100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479443506573123, 362479492926737738⟩, ⟨317268246161238495, 319208826182364867⟩, true⟩

def words02 : List Nat := [371284985124897662, 371284985127080070, 371284985002656502, 371284984997700425, 371284984992140618, 371284984956438488, 371284984525416546, 371284984325044138, 371284984217088523, 371284984219120026]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 58120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 58100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477220289963829, 362477269727993638⟩, ⟨446535422335690042, 448477040948239558⟩, true⟩

def words03 : List Nat := [371284984126138365, 371284984032842636, 371284984091390222, 371284984099192360, 371284984100604534, 371284984061764551, 371284984022235448, 371284983981770871, 371284983601623141, 371284983471388001]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 58130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 58100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478309851495518, 362478359307035177⟩, ⟨383235287409282503, 385177924135118797⟩, true⟩

def words04 : List Nat := [371284983462580531, 371284983464577808, 371284983343491887, 371284983221706357, 371284983099144455, 371284983031042722, 371284982976377296, 371284983098524209, 371284983172999453, 371284983175034062]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 58140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 58100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk581A
