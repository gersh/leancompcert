import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk336A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593245995636621, 360593252850978862⟩, ⟨(-406769904269382904), (-406614164316854194)⟩, true⟩

def state01 : KState := ⟨⟨360560466332810699, 360560473192380512⟩, ⟨694843579254978051, 694999461275599625⟩, true⟩

def words00 : List Nat := [360581152843837537, 360581153513626364, 360581153625091815, 360581153736599431, 360581153736979803, 360581153075822810, 360581152864076183, 360581152627450630, 360581152390791273, 360581151545884696]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360641919440123356, 360641926303933882⟩, ⟨(-2043387763118392890), (-2043231738546479780)⟩, true⟩

def words01 : List Nat := [360581150931023549, 360581150246086688, 360581149759407938, 360581149976639697, 360581149977058274, 360581149449452128, 360581149277334113, 360581150202134045, 360581152010234080, 360581153818328265]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360651922839134700, 360651929707230835⟩, ⟨(-2380087117491335001), (-2379930948816391177)⟩, true⟩

def words02 : List Nat := [360581154947194133, 360581155195141701, 360581156326354361, 360581157457635709, 360581158322249472, 360581159428613651, 360581159862808838, 360581160297032334, 360581161614275634, 360581163719040880]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360610281038114615, 360610287910440647⟩, ⟨(-979490154253737171), (-979333843305988255)⟩, true⟩

def words03 : List Nat := [360581166045054901, 360581168371014873, 360581170077231661, 360581171214085336, 360581171698687316, 360581172183372616, 360581173550669367, 360581174860931268, 360581175726761357, 360581176592605090]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360630418652378572, 360630425528956817⟩, ⟨(-1656779347077221211), (-1656622893064491479)⟩, true⟩

def words04 : List Nat := [360581178340870375, 360581180788864229, 360581183522545895, 360581186256152187, 360581188235964825, 360581189336024298, 360581191318228437, 360581193300446318, 360581194536126354, 360581195999579845]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk336A
