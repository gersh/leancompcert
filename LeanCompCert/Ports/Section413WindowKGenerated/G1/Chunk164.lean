import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk164

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362539764048248133, 362539767586564155⟩, ⟨(-896245819166573755), (-896206567132910923)⟩, true⟩

def state01 : KState := ⟨⟨362478807369391003, 362478810912222487⟩, ⟨103485057172415277, 103524383283244873⟩, true⟩

def words00 : List Nat := [371285126187633894, 371285126188134322, 371285124534067188, 371285125201692368, 371285126264523087, 371285126265025915, 371285123823801682, 371285121385071044, 371285119527330828, 371285119527900930]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 16400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 16400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362454602695769972, 362454606243104687⟩, ⟨501108604994436936, 501148005025983188⟩, true⟩

def words01 : List Nat := [371285122474812303, 371285125805933474, 371285129117137655, 371285129117638891, 371285128527714565, 371285127945920070, 371285130494699413, 371285130495200284, 371285128686364022, 371285126828063639]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 16410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 16400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362509569288017523, 362509572839839761⟩, ⟨(-401461852655653417), (-401422378916081485)⟩, true⟩

def words02 : List Nat := [371285126823063748, 371285127687809847, 371285130423055590, 371285133158173349, 371285135455316348, 371285135455817876, 371285135393939546, 371285137218063700, 371285140558193435, 371285142045675311]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 16420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 16400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362519873600685934, 362519877157082301⟩, ⟨(-570617908684436190), (-570578359768689426)⟩, true⟩

def words03 : List Nat := [371285143512473878, 371285144979271688, 371285150151945567, 371285154116400035, 371285158913173575, 371285163709558767, 371285168484979217, 371285168485480926, 371285170443576620, 371285172555186511]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 16430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 16400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468137970430140, 362468141531301212⟩, ⟨280094755860739321, 280134378363876337⟩, true⟩

def words04 : List Nat := [371285177375388392, 371285177375890183, 371285177270570211, 371285176201177874, 371285175131733289, 371285173554607775, 371285170424916516, 371285170710066529, 371285170976265410, 371285170976794457]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 16440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 16400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362574014118104156, 362574017683505103⟩, ⟨(-1461985373599433552), (-1461945676556612758)⟩, true⟩

def words05 : List Nat := [371285172604135655, 371285175266573494, 371285181625177263, 371285184222486040, 371285186300432551, 371285188378291895, 371285191970218919, 371285194201436124, 371285199598100727, 371285204994327252]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 16450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 16400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487736564247055, 362487740134183702⟩, ⟨(-41603137320175170), (-41563365597298048)⟩, true⟩

def words06 : List Nat := [371285210186186485, 371285210464415571, 371285213652333030, 371285216840138996, 371285220528295284, 371285220528797797, 371285219305849543, 371285217403262555, 371285216553423476, 371285216707215255]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 16460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 16400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362460470215673667, 362460473790145674⟩, ⟨407544673508009683, 407584519951300863⟩, true⟩

def words07 : List Nat := [371285217739389455, 371285218771639240, 371285219274893699, 371285219275396408, 371285214872497237, 371285211640669896, 371285208862558393, 371285208863073224, 371285207360783278, 371285205860531069]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 16470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 16400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362511570276375565, 362511573855346880⟩, ⟨(-434593724070002603), (-434553803455021767)⟩, true⟩

def words08 : List Nat := [371285206543408295, 371285207199006937, 371285210904476541, 371285214609698238, 371285217283964914, 371285217284468155, 371285216514238970, 371285217969628079, 371285221289424117, 371285222887943144]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 16480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 16400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362509358963510735, 362509362547069676⟩, ⟨(-397941291861892787), (-397901295574101011)⟩, true⟩

def words09 : List Nat := [371285224151343722, 371285225414766250, 371285230355484188, 371285233470859409, 371285237657312365, 371285241843456211, 371285245904176201, 371285245904679977, 371285247316413383, 371285248778475403]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 16490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 16400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 16400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk164
