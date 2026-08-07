import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk766

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475778260252903, 362475865951400932⟩, ⟨711183946570676720, 715720004104294284⟩, true⟩

def state01 : KState := ⟨⟨362481648845739249, 362481736560576448⟩, ⟨261489807656104654, 266027679892988160⟩, true⟩

def words00 : List Nat := [371285209434433090, 371285209371372208, 371285209272281747, 371285209309839712, 371285209319235790, 371285209321875897, 371285209103997969, 371285209057887924, 371285209050726969, 371285209053461098]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 76600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 76600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477992980132706, 362478080718948258⟩, ⟨541604048606388162, 546143757950569294⟩, true⟩

def words01 : List Nat := [371285209010108146, 371285208967659723, 371285208999411163, 371285209002320747, 371285209001920663, 371285208988993736, 371285208975169548, 371285208960930001, 371285208761726415, 371285208671936389]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 76610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 76600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477788917747576, 362477876680127366⟩, ⟨557306309577232949, 561847824533349885⟩, true⟩

def words02 : List Nat := [371285208645234878, 371285208647934519, 371285208615892896, 371285208584828998, 371285208568467344, 371285208571428623, 371285208581715907, 371285208633012746, 371285208635022057, 371285208636600463]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 76620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 76600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362497236471821125, 362497324258100608⟩, ⟨(-933043647231057393), (-928500300723988927)⟩, true⟩

def words03 : List Nat := [371285208617173726, 371285208694819263, 371285208932352191, 371285208943881738, 371285208945954425, 371285208937728391, 371285209005453034, 371285209008364230, 371285209167663525, 371285209328745251]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 76630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 76600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484345962644022, 362484433772787271⟩, ⟨54877999287812445, 59423174834080533⟩, true⟩

def words04 : List Nat := [371285209475655531, 371285209478297002, 371285209398255232, 371285209390535064, 371285209422696131, 371285209425343403, 371285209291981724, 371285209147035579, 371285209023140184, 371285209026209764]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 76640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 76600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk766
