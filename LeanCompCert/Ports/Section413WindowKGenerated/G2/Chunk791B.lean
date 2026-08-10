import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk791A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk791B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk791A

def state06 : KState := ⟨⟨360609351199718607, 360609391981241068⟩, ⟨(-2154853727577449441), (-2152673397629781355)⟩, true⟩

def words05 : List Nat := [360582196798060452, 360582196886910473, 360582197134763902, 360582197314175939, 360582197359043437, 360582197404015211, 360582197496163012, 360582197681632883, 360582198026083120, 360582198370780996]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 79150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 79100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581813602293859, 360581854394607542⟩, ⟨25039083595359957, 27220267826994489⟩, true⟩

def words06 : List Nat := [360582198635530071, 360582198741135131, 360582198802876172, 360582198864944095, 360582198865890911, 360582198856677281, 360582198773030735, 360582198568998678, 360582198364757742, 360582198215092916]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 79160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 79100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567408324123160, 360567449127079135⟩, ⟨1165600177414458346, 1167782204250522578⟩, true⟩

def words07 : List Nat := [360582198301773574, 360582198393010976, 360582198394030620, 360582198389878285, 360582198291506650, 360582198151417375, 360582198011015580, 360582197866865412, 360582197761331501, 360582197576236126]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 79170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 79100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360590344160974011, 360590384974607081⟩, ⟨(-650521519077206921), (-648338646775848525)⟩, true⟩

def words08 : List Nat := [360582197390888286, 360582197431183443, 360582197545607855, 360582197660261835, 360582197661305381, 360582197639435902, 360582197680746206, 360582197781790763, 360582197845682625, 360582197950238456]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 79180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 79100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360595973627472661, 360596014451910444⟩, ⟨(-1096371279028645886), (-1094187551049628058)⟩, true⟩

def words09 : List Nat := [360582197951274780, 360582197929815364, 360582198044732094, 360582198276608385, 360582198440059759, 360582198603696623, 360582198687499682, 360582198775859341, 360582198951215326, 360582199126964426]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 79190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 79100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 79100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk791B
