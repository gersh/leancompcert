import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk232A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360516794980259474, 360516798145688916⟩, ⟨1482421739370864308, 1482471424148224430⟩, true⟩

def state01 : KState := ⟨⟨360650756880244461, 360650760048517184⟩, ⟨(-1626173283894104247), (-1626123533138589297)⟩, true⟩

def words00 : List Nat := [360580695022108196, 360580694169387705, 360580696070351160, 360580697971208193, 360580698078115481, 360580698078416973, 360580697151799814, 360580697055355004, 360580698715452843, 360580701734220576]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 23200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 23200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360648545293311446, 360648548464459747⟩, ⟨(-1574764678267561201), (-1574714860756089555)⟩, true⟩

def words01 : List Nat := [360580703808223507, 360580705882083245, 360580709310633243, 360580713839800601, 360580717892394118, 360580721944687556, 360580724921135218, 360580728365636254, 360580731286646931, 360580734207504574]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 23210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 23200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360682570518196566, 360682573692184350⟩, ⟨(-2365201426443631560), (-2365151542985248422)⟩, true⟩

def words02 : List Nat := [360580737395734757, 360580739981552793, 360580741637747026, 360580743293831499, 360580744449488673, 360580747037499001, 360580751475557676, 360580755913291743, 360580759161394599, 360580763544408308]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 23220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 23200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360667873274503098, 360667876451343622⟩, ⟨(-2023863871692353008), (-2023813921950367768)⟩, true⟩

def words03 : List Nat := [360580768464846888, 360580773384950913, 360580778237173222, 360580781249964933, 360580782684179426, 360580784118294212, 360580786333617643, 360580789488263273, 360580793235795790, 360580796983078472]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 23230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 23200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593817410475541, 360593820590189367⟩, ⟨(-302846829893165020), (-302796813361806462)⟩, true⟩

def words04 : List Nat := [360580799585294088, 360580800349199449, 360580801382258210, 360580802415316025, 360580802973258562, 360580802973560567, 360580802391752989, 360580800215303114, 360580798038983003, 360580797631462353]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 23240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 23200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk232A
