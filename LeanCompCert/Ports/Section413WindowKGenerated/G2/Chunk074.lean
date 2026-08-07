import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk074

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360526408948708593, 360526409237521860⟩, ⟨440260647158753895, 440262096432577743⟩, true⟩

def state01 : KState := ⟨⟨360461589381057731, 360461589670696748⟩, ⟨918877927058673272, 918879382447130340⟩, true⟩

def words00 : List Nat := [360585896076733413, 360585878947457493, 360585843786057493, 360585811176265959, 360585778575259294, 360585741146971308, 360585709271651017, 360585667956192227, 360585626651869866, 360585594985466942]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 7400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 7400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360373684833604869, 360373685124063050⟩, ⟨1571400115496206323, 1571401576958864381⟩, true⟩

def words01 : List Nat := [360585579541075795, 360585580828955986, 360585580829034688, 360585567736469559, 360585552987731277, 360585533441615411, 360585513900744204, 360585512356281235, 360585492857757714, 360585464312332439]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 7410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 7400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360324296686295162, 360324296977574511⟩, ⟨1938775144659241826, 1938776612219038366⟩, true⟩

def words02 : List Nat := [360585435774579442, 360585416732526815, 360585406878116047, 360585401740402934, 360585396604068213, 360585373618640256, 360585341457115898, 360585308675428076, 360585275902540870, 360585235956338850]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 7420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 7400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360310252093908213, 360310252386017251⟩, ⟨2043601485723061628, 2043602959451550624⟩, true⟩

def words03 : List Nat := [360585200841495379, 360585156734759629, 360585112639875192, 360585086458885086, 360585075206004690, 360585059210633048, 360585043219552639, 360585014090898216, 360584967127072969, 360584930203147836]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 7430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 7400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360175607573088497, 360175607866020562⟩, ⟨3045569884653430925, 3045571364509426497⟩, true⟩

def words04 : List Nat := [360584893289119848, 360584855792377515, 360584805069776841, 360584745045000203, 360584685036334317, 360584620339772178, 360584568584504826, 360584519431588461, 360584470291858549, 360584409391458069]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 7440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 7400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360476677447119806, 360476677740876763⟩, ⟨800522325080852541, 800523811086403643⟩, true⟩

def words05 : List Nat := [360584354526205381, 360584317481577448, 360584280446864155, 360584251972641154, 360584205723153033, 360584142244903830, 360584078783663237, 360584033114278524, 360584000949136771, 360583986562738212]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 7450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 7400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360302227306505245, 360302227601097965⟩, ⟨2102918542750400680, 2102920034994832226⟩, true⟩

def words06 : List Nat := [360583972180184335, 360583948576054957, 360583935621447804, 360583928115885921, 360583920612312022, 360583908467991613, 360583878577331245, 360583837171553375, 360583795776847949, 360583743000695667]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 7460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 7400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360067729793156097, 360067730088575485⟩, ⟨3856261407000371513, 3856262905424117403⟩, true⟩

def words07 : List Nat := [360583705319680001, 360583677275855820, 360583649239527577, 360583610048672219, 360583563593945287, 360583503799885393, 360583444021792709, 360583401946662569, 360583342189757367, 360583273257749833]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 7470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 7400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360481602446585348, 360481602742834658⟩, ⟨758002381153015041, 758003885788796087⟩, true⟩

def words08 : List Nat := [360583204344150480, 360583153121825879, 360583114078507867, 360583074476406771, 360583034884880552, 360582980062721479, 360582918594962750, 360582874791736916, 360582831000182437, 360582804863767742]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 7480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 7400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360447848124435407, 360447848421521825⟩, ⟨1010629888410909351, 1010631399320836859⟩, true⟩

def words09 : List Nat := [360582791354018711, 360582763587390357, 360582735828156720, 360582717933393271, 360582709078176683, 360582695627048103, 360582682179500595, 360582652818252269, 360582617243840735, 360582599274764604]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 7490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 7400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 7400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk074
