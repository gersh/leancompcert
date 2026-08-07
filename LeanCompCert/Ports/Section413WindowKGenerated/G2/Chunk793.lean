import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk793

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567349087862891, 360567390019417730⟩, ⟨1172449776430872414, 1174641993434042160⟩, true⟩

def state01 : KState := ⟨⟨360602237857686007, 360602278799950984⟩, ⟨(-1594460320276522063), (-1592267253906509941)⟩, true⟩

def words00 : List Nat := [360582202469022159, 360582202493709572, 360582202542243599, 360582202590979093, 360582202592027144, 360582202487142247, 360582202313400288, 360582202255984370, 360582202298258732, 360582202552596815]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 79300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 79300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590268041256761, 360590308994297283⟩, ⟨(-645079658536454347), (-642885737502649995)⟩, true⟩

def words01 : List Nat := [360582202727305819, 360582202902133978, 360582203124197481, 360582203426045713, 360582203652029382, 360582203878191480, 360582203981347302, 360582203982480719, 360582204029092314, 360582204132564544]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 79310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 79300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584370370182736, 360584411333901873⟩, ⟨(-177273337457764676), (-175078569344031112)⟩, true⟩

def words02 : List Nat := [360582204260298039, 360582204335880574, 360582204336890573, 360582204323327266, 360582204309562978, 360582204220649978, 360582204299502556, 360582204378569699, 360582204379580493, 360582204396269119]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 79320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 79300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591942980449235, 360591983954883541⟩, ⟨(-778080389233498039), (-775884771032855141)⟩, true⟩

def words03 : List Nat := [360582204420838116, 360582204445731396, 360582204628896409, 360582204653741352, 360582204654797624, 360582204529339041, 360582204435681468, 360582204591173299, 360582204715355629, 360582204839785007]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 79330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 79300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574625282653853, 360574666267877170⟩, ⟨595841345445871107, 598037819699450491⟩, true⟩

def words04 : List Nat := [360582204873667221, 360582204874800946, 360582204750080841, 360582204650355503, 360582204550333247, 360582204340975131, 360582204019633216, 360582203619036764, 360582203218233173, 360582202976379999]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 79340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 79300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360560384622596546, 360560425618513843⟩, ⟨1725982620461514828, 1728179943336590302⟩, true⟩

def words05 : List Nat := [360582202906178102, 360582202931197294, 360582202932218053, 360582202878179667, 360582202800077480, 360582202648749059, 360582202503046126, 360582202504180055, 360582202352723022, 360582202079493387]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 79350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 79300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594305380692122, 360594346387311742⟩, ⟨(-966155029643300006), (-963956857378111292)⟩, true⟩

def words06 : List Nat := [360582201806012880, 360582201645420215, 360582201564294813, 360582201553893914, 360582201543418060, 360582201367604583, 360582201195880892, 360582201182987010, 360582201282730995, 360582201436922077]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 79360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 79300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587249841075725, 360587290858530145⟩, ⟨(-406203878205520459), (-404004845931902059)⟩, true⟩

def words07 : List Nat := [360582201510991299, 360582201585172704, 360582201586110556, 360582201549765036, 360582201550715732, 360582201521053658, 360582201491260638, 360582201382258396, 360582201352967626, 360582201418413091]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 79370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 79300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583480990273602, 360583522018400541⟩, ⟨(-107011374651459207), (-104811495138950407)⟩, true⟩

def words08 : List Nat := [360582201610542360, 360582201734210310, 360582201764037753, 360582201793987716, 360582201794937334, 360582201871475648, 360582201876499268, 360582201881717840, 360582201882738352, 360582201824737041]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 79380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 79300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360622443131930239, 360622484170767601⟩, ⟨(-3200488511915040036), (-3198287782049443582)⟩, true⟩

def words09 : List Nat := [360582201838341587, 360582201852273730, 360582202024261724, 360582202237513022, 360582202308425681, 360582202379426010, 360582202608580441, 360582202958809233, 360582203467046775, 360582203975530143]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 79390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 79300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 79300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk793
