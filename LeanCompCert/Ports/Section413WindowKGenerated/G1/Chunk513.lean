import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk513

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485073540610171, 362485111646108871⟩, ⟨(-5933643504931342), (-4613010341633874)⟩, true⟩

def state01 : KState := ⟨⟨362477546449521572, 362477584570308070⟩, ⟨380223761680281557, 381545179187298751⟩, true⟩

def words00 : List Nat := [371285021967343315, 371285021969058533, 371285021757228811, 371285021462352907, 371285021166805700, 371285020959246762, 371285020613078452, 371285020630875075, 371285020646833139, 371285020648639532]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 51300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 51300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478942824691627, 362478980960991094⟩, ⟨308590695385587627, 309912908943278821⟩, true⟩

def words01 : List Nat := [371285020613096724, 371285020723376269, 371285021060484186, 371285021062199750, 371285020893743968, 371285020616684693, 371285020338975406, 371285020219350658, 371285019909709295, 371285019793979077]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 51310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 51300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362472241216442092, 362472279368230549⟩, ⟨652463830261328682, 653786838790870146⟩, true⟩

def words02 : List Nat := [371285019677594580, 371285019562283965, 371285018996709604, 371285018672905149, 371285018348241032, 371285018135238820, 371285017581909135, 371285017029362936, 371285016476116835, 371285016302553380]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 51320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 51300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362452016844208552, 362452055011458786⟩, ⟨1690714252230847060, 1692038054490158486⟩, true⟩

def words03 : List Nat := [371285016055605322, 371285015966673085, 371285015877180906, 371285015771379373, 371285015159757439, 371285014666019853, 371285014171388090, 371285013781240468, 371285013151587574, 371285012511546246]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 51330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 51300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481624135340101, 362481662317949076⟩, ⟨170568058100724721, 171892648956342213⟩, true⟩

def words04 : List Nat := [371285011870778253, 371285011609463656, 371285011179144949, 371285011128242075, 371285011076821114, 371285010920597589, 371285010258723477, 371285009976383946, 371285009787416174, 371285009789204312]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 51340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 51300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362463920562549055, 362463958760843377⟩, ⟨1079850794166032777, 1081176190540268951⟩, true⟩

def words05 : List Nat := [371285009725300544, 371285009662571999, 371285009860222297, 371285009937475872, 371285010130914660, 371285010324987917, 371285010467542996, 371285010469260454, 371285010106858853, 371285009699132713]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 51350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 51300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468187342242659, 362468225555824221⟩, ⟨860706172302491804, 862032353911093348⟩, true⟩

def words06 : List Nat := [371285009290436188, 371285009260687676, 371285008781231140, 371285008301161365, 371285007820469302, 371285007457441127, 371285006955232692, 371285006772656224, 371285006589492978, 371285006407564753]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 51360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 51300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490874405873885, 362490912634990277⟩, ⟨(-304865022346030172), (-303538042634589810)⟩, true⟩

def words07 : List Nat := [371285006082071219, 371285006079822612, 371285006151206709, 371285006152929490, 371285005840942181, 371285005459171299, 371285005076682385, 371285005038370669, 371285004924934908, 371285005041859848]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 51370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 51300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362463225942991898, 362463264187608120⟩, ⟨1115836207348361560, 1117163983521956906⟩, true⟩

def words08 : List Nat := [371285005082604244, 371285005084325097, 371285004729944238, 371285004743259670, 371285004833774734, 371285004835493233, 371285004421823030, 371285003935529103, 371285003448576118, 371285003124823959]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 51380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 51300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362457284724211178, 362457322984313935⟩, ⟨1421246063185712740, 1422574635290889708⟩, true⟩

def words09 : List Nat := [371285002702983072, 371285002522346888, 371285002341102022, 371285002129648124, 371285001603421248, 371285001159400867, 371285000714527326, 371285000606113910, 371285000070155332, 371284999533638661]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 51390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 51300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 51300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk513
