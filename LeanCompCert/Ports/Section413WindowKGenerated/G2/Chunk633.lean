import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk633

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360577750852128877, 360577776470641695⟩, ⟨311029347481027363, 312124817242655657⟩, true⟩

def state01 : KState := ⟨⟨360556991150380607, 360557016777283950⟩, ⟨1625161285086317602, 1626257286009432650⟩, true⟩

def words00 : List Nat := [360582707275266509, 360582707192025385, 360582706960493804, 360582706603594341, 360582706246565726, 360582705726714828, 360582705333154239, 360582704932419903, 360582704531581370, 360582703987614221]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 63300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 63300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589864623360935, 360589890258652451⟩, ⟨(-456234228502936070), (-455137696482964246)⟩, true⟩

def words01 : List Nat := [360582703582602884, 360582703427012682, 360582703363745516, 360582703364635158, 360582703209570762, 360582702806625280, 360582702403516204, 360582702249796958, 360582702359808615, 360582702474244704]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 63310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 63300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360557878323687372, 360557903967462698⟩, ⟨1569263617280337198, 1570360686537499238⟩, true⟩

def words02 : List Nat := [360582702475037307, 360582702464031277, 360582702525958625, 360582702593893253, 360582702594640748, 360582702501614935, 360582702160099026, 360582701602621078, 360582701045003015, 360582700441275070]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 63320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 63300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360545879983175522, 360545905635329266⟩, ⟨2329218830839852141, 2330316430743457267⟩, true⟩

def words03 : List Nat := [360582700050456869, 360582699908816164, 360582699767090710, 360582699474601467, 360582698933610602, 360582698288672788, 360582697643471730, 360582697247429181, 360582696812524897, 360582696232593925]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 63330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 63300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569404279115341, 360569429939686854⟩, ⟨839095973168984467, 840194106293601103⟩, true⟩

def words04 : List Nat := [360582695652479726, 360582695255026556, 360582695056145214, 360582694851172949, 360582694646137785, 360582694205641434, 360582693655525983, 360582693354566308, 360582693053363408, 360582692672225033]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 63340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 63300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360562790397776829, 360562816066826327⟩, ⟨1258163548288586516, 1259262218536872168⟩, true⟩

def words05 : List Nat := [360582692463672378, 360582692131410284, 360582691798988251, 360582691755721257, 360582691756466322, 360582691734648615, 360582691712748227, 360582691496134251, 360582691098837228, 360582690786184548]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574733504063285, 360574759181490497⟩, ⟨501392328326929477, 502491529429286809⟩, true⟩

def words06 : List Nat := [360582690473230057, 360582690409235942, 360582690271382651, 360582690008412411, 360582689745292362, 360582689283490199, 360582688974445148, 360582688914305314, 360582688854078289, 360582688667515893]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588648598877202, 360588674284722269⟩, ⟨(-380613960522763360), (-379514225939551360)⟩, true⟩

def words07 : List Nat := [360582688543125381, 360582688287654094, 360582688031929761, 360582687972484225, 360582687664980670, 360582687144549713, 360582686623962272, 360582686352331490, 360582686366067137, 360582686461463887]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596485638898260, 360596511333220758⟩, ⟨(-877474855681073979), (-876374583756850075)⟩, true⟩

def words08 : List Nat := [360582686462257744, 360582686394105444, 360582686584400186, 360582686780466974, 360582686805800213, 360582686806691320, 360582686687958024, 360582686445676017, 360582686208624673, 360582686427733278]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571089025232962, 360571114727954734⟩, ⟨732633475903050348, 733734280299670538⟩, true⟩

def words09 : List Nat := [360582686895094002, 360582687362626072, 360582687608968330, 360582687722219170, 360582687730439296, 360582687738904666, 360582687995615136, 360582688004671495, 360582688005479052, 360582687823858515]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk633
