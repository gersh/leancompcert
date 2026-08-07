import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk067

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362326600466000070, 362326601009842350⟩, ⟨1047691708380376064, 1047694176176452832⟩, true⟩

def state01 : KState := ⟨⟨362600649753038421, 362600650298573518⟩, ⟨(-789557158677799806), (-789554679531133324)⟩, true⟩

def words00 : List Nat := [371282949939410822, 371282948846411059, 371282946948325504, 371282957114282682, 371282962814953369, 371282962815145798, 371282953504988899, 371282956625071217, 371282981940771006, 371282999474623119]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 6700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 6700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362542852894900235, 362542853442164543⟩, ⟨(-401418183962397682), (-401415693204125150)⟩, true⟩

def words01 : List Nat := [371283016766936415, 371283034054163106, 371283059667245718, 371283074300347105, 371283090712228476, 371283107119293599, 371283123311386965, 371283123311576667, 371283118963768539, 371283127851745837]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 6710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 6700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362325763591961893, 362325764140914343⟩, ⟨1058475259268964927, 1058477761380451169⟩, true⟩

def words02 : List Nat := [371283141935138389, 371283141935328173, 371283126616047851, 371283111328210541, 371283096044849441, 371283086995078863, 371283069743438309, 371283060442353197, 371283051143967109, 371283041668608318]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 6720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 6700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362671047047790467, 362671047598459766⟩, ⟨(-1266820218570313476), (-1266817704895721728)⟩, true⟩

def words03 : List Nat := [371283018302591709, 371283012316939309, 371283022380433237, 371283026751001738, 371283027919171108, 371283029087054990, 371283052265326894, 371283064558365542, 371283092449153888, 371283120331749231]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 6730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 6700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362399218169820920, 362399218722211129⟩, ⟨566132824903231383, 566135350185526559⟩, true⟩

def words04 : List Nat := [371283143643959816, 371283143644150231, 371283142702719378, 371283147678891038, 371283157128748911, 371283157128939420, 371283137387098681, 371283117415182442, 371283097449106434, 371283090625942319]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 6740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 6700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362339986785814315, 362339987339921476⟩, ⟨966826677461960923, 966829214342514899⟩, true⟩

def words05 : List Nat := [371283082657043732, 371283087110531946, 371283091385065873, 371283091385257819, 371283076552658239, 371283063171734782, 371283051751126220, 371283051751317266, 371283030573074107, 371283009413049067]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 6750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 6700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362463390238366789, 362463390794186156⟩, ⟨132906984181825965, 132909532645566505⟩, true⟩

def words06 : List Nat := [371282988954112812, 371282988954326648, 371282998583289363, 371283014312257554, 371283021858002076, 371283021858193699, 371283009968558327, 371283012119727541, 371283022925841459, 371283022926039268]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 6760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 6700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362457432654162187, 362457433211720639⟩, ⟨173309662062835145, 173312222309165715⟩, true⟩

def words07 : List Nat := [371283020026738984, 371283014174517195, 371283016474629379, 371283016474839855, 371283017610020296, 371283021369016851, 371283024764346557, 371283024764538012, 371282999256966641, 371282995486397508]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 6770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 6700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362344256280277370, 362344256839546257⟩, ⟨941301162191250455, 941303734043046395⟩, true⟩

def words08 : List Nat := [371283009671229843, 371283009671421444, 371282998744310799, 371282981270092877, 371282963800950620, 371282947100971639, 371282923909813960, 371282911539941820, 371282899173651380, 371282887728212391]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 6780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 6700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362555008186701468, 362555008747706237⟩, ⟨(-490381863770033102), (-490379280122837838)⟩, true⟩

def words09 : List Nat := [371282868564620441, 371282869814674105, 371282892715982929, 371282892716175065, 371282892111292016, 371282887486668709, 371282886898454345, 371282886898667103, 371282894147469535, 371282904751217069]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 6790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 6700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 6700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk067
