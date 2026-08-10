import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk766A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk766B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk766A

def state06 : KState := ⟨⟨362464593057624456, 362464680891495673⟩, ⟨1569125019123232145, 1573672013543298435⟩, true⟩

def words05 : List Nat := [371285209177811356, 371285209340574197, 371285209474666413, 371285209477308112, 371285209384522896, 371285209345157997, 371285209312282376, 371285209314924175, 371285209098071802, 371285208833232476]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 76650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 76600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479628790065691, 362479716647582664⟩, ⟨416410410648331665, 420959217872608843⟩, true⟩

def words06 : List Nat := [371285208567257265, 371285208415507721, 371285208178161269, 371285208085024012, 371285207990995345, 371285207880325404, 371285207542160004, 371285207375293185, 371285207207090452, 371285207181270843]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 76660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 76600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490484637477622, 362490572519139991⟩, ⟨(-415970160626115686), (-411419502056146058)⟩, true⟩

def words07 : List Nat := [371285207111687684, 371285207009965288, 371285206972433404, 371285206977563981, 371285207033072783, 371285207089568968, 371285207133073656, 371285207135762485, 371285207107591010, 371285207180893801]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 76670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 76600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473937352501582, 362474025257681279⟩, ⟨852980036195241147, 857532498199210569⟩, true⟩

def words08 : List Nat := [371285207340812094, 371285207343458804, 371285207320656207, 371285207298821373, 371285207276025466, 371285207262628131, 371285207163099256, 371285207129780913, 371285207095554496, 371285207061021992]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 76680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 76600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492364883391329, 362492452812470626⟩, ⟨(-560295725532993609), (-555741430549010323)⟩, true⟩

def words09 : List Nat := [371285206917011697, 371285206918627225, 371285207076601428, 371285207079246909, 371285207046758018, 371285206987789976, 371285207035698088, 371285207062229775, 371285207158522533, 371285207255951820]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 76690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 76600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 76600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk766B
