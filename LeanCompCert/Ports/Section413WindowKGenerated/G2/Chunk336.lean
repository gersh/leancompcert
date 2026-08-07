import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk336

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

def state06 : KState := ⟨⟨360614141674705127, 360614148555570618⟩, ⟨(-1108930427697658196), (-1108773829398700720)⟩, true⟩

def words05 : List Nat := [360581197020831620, 360581198042068234, 360581199702825570, 360581201906109212, 360581203721718934, 360581205537301756, 360581206796808100, 360581207177061775, 360581208156076348, 360581209135190989]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360616036219620108, 360616043104727340⟩, ⟨(-1172896869419923688), (-1172740128323251222)⟩, true⟩

def words06 : List Nat := [360581210615529736, 360581211216745397, 360581211217153349, 360581211109975347, 360581211002730397, 360581210831814142, 360581211650691753, 360581212469607708, 360581212687609547, 360581213722519409]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360627758736483214, 360627765625835263⟩, ⟨(-1567751534620661700), (-1567594650579568214)⟩, true⟩

def words07 : List Nat := [360581214889124795, 360581216055790938, 360581217858935773, 360581219039568875, 360581219469935117, 360581219900310574, 360581219956755074, 360581220458860734, 360581221841207266, 360581223223573467]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360604815514832597, 360604822408470355⟩, ⟨(-795106848739190628), (-794949820333812886)⟩, true⟩

def words08 : List Nat := [360581224117022851, 360581224886820265, 360581225908145674, 360581226929548968, 360581227727710872, 360581227728161223, 360581227648523374, 360581227040540021, 360581226432506759, 360581227091610250]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360567514605738292, 360567521503625384⟩, ⟨461691081107534139, 461848252694324225⟩, true⟩

def words09 : List Nat := [360581227767609637, 360581228443648772, 360581228451144432, 360581228451596080, 360581228179425213, 360581227442221775, 360581226704923272, 360581226605362323, 360581226605763834, 360581226199551032]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk336
