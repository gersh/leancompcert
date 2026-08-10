import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk770A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489438713012532, 362489527358045540⟩, ⟨(-337894924849878241), (-333285608699077179)⟩, true⟩

def state01 : KState := ⟨⟨362479193633206797, 362479282302162646⟩, ⟨450989891967611572, 455601050298373776⟩, true⟩

def words00 : List Nat := [371285199088050517, 371285199090705257, 371285198924344921, 371285198927691669, 371285198981313278, 371285198983968212, 371285198831187298, 371285198650154080, 371285198468010422, 371285198430591401]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 77000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 77000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475703213757532, 362475791906568751⟩, ⟨719840678008592379, 724453673567521087⟩, true⟩

def words01 : List Nat := [371285198366317787, 371285198379923959, 371285198394255252, 371285198396956886, 371285198270896916, 371285198189162771, 371285198189513119, 371285198192168804, 371285198071874955, 371285197952706995]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 77010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 77000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485155606999177, 362485244323632490⟩, ⟨(-8205619583235547), (-3590789127473707)⟩, true⟩

def words02 : List Nat := [371285197832416252, 371285197783510595, 371285197730393698, 371285197790051072, 371285197837470713, 371285197840132113, 371285197712457854, 371285197655522436, 371285197705420041, 371285197708774479]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 77020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 77000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481443589664248, 362481532330524169⟩, ⟨277748075910893214, 282364772663068032⟩, true⟩

def words03 : List Nat := [371285197711832210, 371285197715790002, 371285197774576295, 371285197777504538, 371285197757254659, 371285197745212113, 371285197732296780, 371285197720218955, 371285197545725595, 371285197501508893]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 77030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 77000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483598588515249, 362483687353052900⟩, ⟨111752652920405965, 116371173928734313⟩, true⟩

def words04 : List Nat := [371285197576483944, 371285197579186532, 371285197561741501, 371285197533919352, 371285197511733186, 371285197514660492, 371285197529502095, 371285197623082683, 371285197683506394, 371285197686264175]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 77040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 77000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk770A
