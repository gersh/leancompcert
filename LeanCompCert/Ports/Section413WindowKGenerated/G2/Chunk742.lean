import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk742

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

def state06 : KState := ⟨⟨360568204040469671, 360568239749390582⟩, ⟨1044780348139766269, 1046571417237287115⟩, true⟩

def words05 : List Nat := [360582333303100549, 360582333476335807, 360582333549500372, 360582333550556518, 360582333487133016, 360582333378335068, 360582333340269369, 360582333341325581, 360582333277932821, 360582333089240263]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360564291506290447, 360564327225192722⟩, ⟨1335305463718456111, 1337097274082402503⟩, true⟩

def words06 : List Nat := [360582332900319170, 360582332678130587, 360582332547083628, 360582332391547017, 360582332235932665, 360582331925740016, 360582331489185068, 360582331137258475, 360582330785025397, 360582330419942721]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552515562958322, 360552551291913750⟩, ⟨2209952025470859420, 2211744582532534108⟩, true⟩

def words07 : List Nat := [360582330178487325, 360582329827145818, 360582329475606709, 360582329172932777, 360582328961358003, 360582328704460665, 360582328447480741, 360582328047768708, 360582327466781814, 360582327067122858]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567948889056025, 360567984627962687⟩, ⟨1063422856490992337, 1065216152779517195⟩, true⟩

def words08 : List Nat := [360582326667123991, 360582326389243171, 360582326057472989, 360582325587687660, 360582325117724177, 360582324581288830, 360582324134999129, 360582323869853616, 360582323604600179, 360582323248945047]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360604384718853280, 360604420467747727⟩, ⟨(-1643660277241030642), (-1641866238912192880)⟩, true⟩

def words09 : List Nat := [360582323056808081, 360582322860885279, 360582322664657153, 360582322649541443, 360582322616258547, 360582322424902121, 360582322233347968, 360582322372433424, 360582322670704923, 360582322969209186]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk742
