import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk562A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk562B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk562A

def state06 : KState := ⟨⟨360531069867736839, 360531089915461680⟩, ⟨2851308948753783099, 2852070982970129505⟩, true⟩

def words05 : List Nat := [360581789906978595, 360581789522727232, 360581789138391793, 360581788536680158, 360581787888015084, 360581787159509783, 360581786430800709, 360581785930806177, 360581785287531984, 360581784387252831]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 56250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 56200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602186667623938, 360602206722744101⟩, ⟨(-1150122371646680942), (-1149359921332981616)⟩, true⟩

def words06 : List Nat := [360581783486827520, 360581782834210835, 360581782339742879, 360581782160846663, 360581781981897513, 360581781510748288, 360581781047572249, 360581780900018079, 360581780919170367, 360581781282973474]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 56260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 56200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360590670854417382, 360590690917009687⟩, ⟨(-502103602385525307), (-501340731577791539)⟩, true⟩

def words07 : List Nat := [360581781488558052, 360581781694220883, 360581781891569883, 360581782257237273, 360581782540550949, 360581782823986950, 360581782870661628, 360581782871446994, 360581782942902527, 360581783102088528]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 56270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 56200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566122416200299, 360566142486170257⟩, ⟨879592634367508655, 880355920426241467⟩, true⟩

def words08 : List Nat := [360581783409891547, 360581783483016215, 360581783483714521, 360581783379721125, 360581783275603563, 360581783111675466, 360581783112326574, 360581782851389224, 360581782590376230, 360581782136559780]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 56280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 56200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360615364004518474, 360615384081884153⟩, ⟨(-1892511861672344416), (-1891748159271279412)⟩, true⟩

def words09 : List Nat := [360581781859357921, 360581781837884155, 360581781978347077, 360581782149266541, 360581782149996919, 360581782050541461, 360581781990200733, 360581782272958574, 360581782870427429, 360581783468053648]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 56290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 56200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 56200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk562B
