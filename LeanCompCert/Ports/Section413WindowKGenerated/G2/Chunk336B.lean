import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk336A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk336B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk336A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk336B
