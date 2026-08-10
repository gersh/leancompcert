import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk793A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk793B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk793A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk793B
