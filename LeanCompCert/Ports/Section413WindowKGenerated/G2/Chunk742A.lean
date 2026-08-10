import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk742A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360551369659859575, 360551405308835857⟩, ⟨2292731977463465641, 2294518596877535279⟩, true⟩

def state01 : KState := ⟨⟨360589763449265405, 360589799108196800⟩, ⟨(-556259424641252629), (-554472066508221857)⟩, true⟩

def words00 : List Nat := [360582328324161666, 360582328089914724, 360582328010885311, 360582328062667758, 360582328063653017, 360582327927521259, 360582327764709023, 360582327598095425, 360582327444706486, 360582327546480772]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591340776722290, 360591376445705831⟩, ⟨(-673332755017836309), (-671544650866628771)⟩, true⟩

def words01 : List Nat := [360582327547422036, 360582327535523358, 360582327634251838, 360582327885753968, 360582328091212324, 360582328296837221, 360582328351847933, 360582328352903921, 360582328416330538, 360582328539441208]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598183619281996, 360598219298222376⟩, ⟨(-1181305478026903383), (-1179516634830312073)⟩, true⟩

def words02 : List Nat := [360582328603105395, 360582328698973184, 360582328704122756, 360582328709377522, 360582328710262132, 360582328730180488, 360582328944296282, 360582329158634105, 360582329271058982, 360582329486218897]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360602693924732264, 360602729613632107⟩, ⟨(-1516097931991766394), (-1514308349454122014)⟩, true⟩

def words03 : List Nat := [360582329882322774, 360582330278736729, 360582330754706807, 360582331049533518, 360582331166663082, 360582331283854353, 360582331528280646, 360582331864542722, 360582332140158661, 360582332415999342]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587048277976829, 360587083976956640⟩, ⟨(-354545463490530100), (-352755132568804294)⟩, true⟩

def words04 : List Nat := [360582332594384711, 360582332778262260, 360582333015886240, 360582333253811338, 360582333416162200, 360582333417218178, 360582333398354962, 360582333288969034, 360582333179398788, 360582333130064763]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk742A
