import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk412A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360545308216314860, 360545318697094544⟩, ⟨1524509363425797106, 1524801197375502272⟩, true⟩

def state01 : KState := ⟨⟨360610176659560633, 360610187145633209⟩, ⟨(-1148267169574012306), (-1147975117532087472)⟩, true⟩

def words00 : List Nat := [360582327537074775, 360582327365536922, 360582328092012298, 360582328818559441, 360582328979637046, 360582329055213869, 360582329571859763, 360582330088646110, 360582330432662571, 360582331109197984]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 41200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 41200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360609897093982030, 360609907585387175⟩, ⟨(-1136733305253735678), (-1136441033429981436)⟩, true⟩

def words01 : List Nat := [360582331420309330, 360582331731460893, 360582332629600075, 360582333822120079, 360582334864897265, 360582335907725528, 360582336501600372, 360582336778752936, 360582337448075583, 360582338117556944]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 41210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 41200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360616019062412324, 360616029559100484⟩, ⟨(-1389233657695480251), (-1388941168079980739)⟩, true⟩

def words02 : List Nat := [360582339373692877, 360582340044107121, 360582340228281928, 360582340412497861, 360582340412968534, 360582340256284594, 360582340911767668, 360582341567329778, 360582341924066282, 360582342741703866]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 41220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 41200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360628933424876457, 360628943926848762⟩, ⟨(-1921632151741756802), (-1921339444234863106)⟩, true⟩

def words03 : List Nat := [360582344145796985, 360582345549986025, 360582347540548079, 360582349143277202, 360582350247103473, 360582351350922625, 360582352273790316, 360582353575797882, 360582354705991626, 360582355836253606]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 41230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 41200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614849479713971, 360614859987023168⟩, ⟨(-1340840459684923225), (-1340547532058889979)⟩, true⟩

def words04 : List Nat := [360582356600422314, 360582357176027281, 360582358337932765, 360582359499956576, 360582360437678746, 360582361040699834, 360582361347593502, 360582361654528743, 360582361864389976, 360582362652848024]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 41240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 41200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk412A
