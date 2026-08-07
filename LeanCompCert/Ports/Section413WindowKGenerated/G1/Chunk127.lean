import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk127

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362429860700255880, 362429862774691819⟩, ⟨695021186866859126, 695039014002592054⟩, true⟩

def state01 : KState := ⟨⟨362486509467116116, 362486511544939212⟩, ⟨(-24516562626590445), (-24498692456627593)⟩, true⟩

def words00 : List Nat := [371284585947456572, 371284585649495045, 371284586764509429, 371284590412529208, 371284591769621537, 371284591770000252, 371284584888285609, 371284582883556804, 371284584031371635, 371284584183405373]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 12700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 12700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362465447537667651, 362465449618952871⟩, ⟨243629716703122059, 243647630893986481⟩, true⟩

def words01 : List Nat := [371284584183689510, 371284583803667652, 371284589213291999, 371284592764677871, 371284598183456323, 371284603601527399, 371284608818366758, 371284608818745918, 371284605812432679, 371284604306916235]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 12710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 12700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362419239080894002, 362419241165556692⟩, ⟨831793983164151605, 831811940334103661⟩, true⟩

def words02 : List Nat := [371284607458090466, 371284607458469717, 371284603896368504, 371284600353632507, 371284596811312581, 371284595139231663, 371284591158607587, 371284588704175388, 371284586249997818, 371284583816014988]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 12720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 12700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488980478971509, 362488982567066947⟩, ⟨(-56573426742841484), (-56555425856603972)⟩, true⟩

def words03 : List Nat := [371284578683710928, 371284578103590686, 371284577825548081, 371284577825927731, 371284569926025961, 371284561209949396, 371284552495082718, 371284548810734961, 371284543365233569, 371284543714083932]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 12730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 12700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362390114578585967, 362390116670106726⟩, ⟨1203525593350050255, 1203543637892193439⟩, true⟩

def words04 : List Nat := [371284544010164724, 371284544010545160, 371284537911601587, 371284537933049514, 371284539816683170, 371284539817063160, 371284533512947630, 371284525919543174, 371284518327182042, 371284512249549251]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 12740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 12700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362382279736126476, 362382281831072190⟩, ⟨1303782627333087007, 1303800715561164423⟩, true⟩

def words05 : List Nat := [371284504846813584, 371284501969874070, 371284499093257321, 371284496302292010, 371284488448301714, 371284482459641730, 371284476611045546, 371284476611425851, 371284468578468837, 371284460570536232]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 12750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 12700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362431675653656958, 362431677752013940⟩, ⟨673341135022508479, 673359266795450201⟩, true⟩

def words06 : List Nat := [371284452563688546, 371284447091448771, 371284438653422137, 371284436336416068, 371284434019659223, 371284429870953970, 371284419958835238, 371284413868386600, 371284407778682166, 371284407530149841]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 12760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 12700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362389264439964233, 362389266541784315⟩, ⟨1215270892254847580, 1215289068269271346⟩, true⟩

def words07 : List Nat := [371284403401571318, 371284397868657285, 371284392336458888, 371284391846141101, 371284388285970895, 371284384991594081, 371284381697601853, 371284378432854773, 371284367024001704, 371284359583119939]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 12770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 12700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362399589750389550, 362399591855608401⟩, ⟨1083705509234896552, 1083723728703295094⟩, true⟩

def words08 : List Nat := [371284352143191028, 371284350804797810, 371284346289540953, 371284341807409216, 371284337325827524, 371284334711636784, 371284329029480307, 371284327873782269, 371284326718147768, 371284323968876837]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 12780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 12700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362506098857622289, 362506100966292853⟩, ⟨(-279122474196781011), (-279104210564003699)⟩, true⟩

def words09 : List Nat := [371284317344781974, 371284316811669973, 371284318864683214, 371284318865064532, 371284313328569571, 371284306747806953, 371284300167915154, 371284298623773705, 371284295949408636, 371284297653226374]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 12790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 12700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 12700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk127
