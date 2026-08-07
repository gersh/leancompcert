import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk485

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362500095560143001, 362500129465576190⟩, ⟨(-730964673511782771), (-729853683136429969)⟩, true⟩

def state01 : KState := ⟨⟨362465150615034627, 362465184535074967⟩, ⟨963921925890178286, 965033624783296318⟩, true⟩

def words00 : List Nat := [371285081510201678, 371285081511816720, 371285081209784464, 371285080952451424, 371285080694316787, 371285080532654683, 371285079863140390, 371285079125174683, 371285078386597741, 371285078033833642]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 48500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 48500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362445086229100785, 362445120163682328⟩, ⟨1937448882687274309, 1938561287048538373⟩, true⟩

def words01 : List Nat := [371285077624847792, 371285077597776385, 371285077570138760, 371285077516509126, 371285076951427831, 371285076492819750, 371285076033423471, 371285075657462952, 371285074845318624, 371285074023679207]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 48510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 48500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362465024873502060, 362465058822550299⟩, ⟨969952267366653993, 971065373726516953⟩, true⟩

def words02 : List Nat := [371285073201348861, 371285072586148206, 371285071757234320, 371285071352303760, 371285070946873546, 371285070480343321, 371285069574722144, 371285069093250092, 371285068610927498, 371285068411953277]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 48520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 48500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475400857168537, 362475434820924135⟩, ⟨466336711246778210, 467450531432489804⟩, true⟩

def words03 : List Nat := [371285068000877340, 371285067503951809, 371285067006393270, 371285066932673835, 371285066645414349, 371285066381674579, 371285066117397879, 371285065850597205, 371285065230186605, 371285065033767821]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 48530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 48500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470334171782947, 362470368149936648⟩, ⟨712349941677392676, 713464460820429668⟩, true⟩

def words04 : List Nat := [371285065061149338, 371285065062773521, 371285064882710865, 371285064616860594, 371285064350401345, 371285064107279780, 371285063714771124, 371285063678612835, 371285063641925140, 371285063607420077]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 48540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 48500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362496812360096491, 362496846352903511⟩, ⟨(-573253817732335550), (-572138587097742164)⟩, true⟩

def words05 : List Nat := [371285063362043095, 371285063420233829, 371285063780190136, 371285063781817896, 371285063761974236, 371285063706532763, 371285063936274795, 371285064011204721, 371285064254956189, 371285064499418251]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 48550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 48500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481756142995713, 362481790150385009⟩, ⟨157899422770544606, 159015361596105672⟩, true⟩

def words06 : List Nat := [371285064744973273, 371285064746590358, 371285064530128544, 371285064634600786, 371285064752088463, 371285064753733695, 371285064518613355, 371285064285831782, 371285064090513168, 371285064092357340]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 48560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 48500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362468321687840581, 362468355709799515⟩, ⟨810565502238586077, 811682148783547037⟩, true⟩

def words07 : List Nat := [371285064381133902, 371285064737943474, 371285065005067824, 371285065006685374, 371285064756726354, 371285064570481008, 371285064549431498, 371285064551049162, 371285064206470156, 371285063864364842]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 48570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 48500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468562765400946, 362468596801822914⟩, ⟨798871294026747886, 799988643261630338⟩, true⟩

def words08 : List Nat := [371285063521544936, 371285063344457597, 371285062957015977, 371285062883013736, 371285062808498154, 371285062655600616, 371285062067586232, 371285061525043517, 371285060981703754, 371285060861161495]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 48580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 48500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486260045725503, 362486294096925620⟩, ⟨(-61099799714571134), (-59981732337903758)⟩, true⟩

def words09 : List Nat := [371285060523553278, 371285060183614699, 371285059923461136, 371285059925283562, 371285059998223038, 371285060101462892, 371285060151800503, 371285060153430473, 371285059902860952, 371285059930296582]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 48590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 48500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 48500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk485
