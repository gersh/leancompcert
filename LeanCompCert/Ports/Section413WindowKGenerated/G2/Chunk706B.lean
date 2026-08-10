import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk706A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk706B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk706A

def state06 : KState := ⟨⟨360557144890926352, 360557177094296345⟩, ⟨1783325500832463229, 1784862501764676001⟩, true⟩

def words05 : List Nat := [360582439409223262, 360582439388794661, 360582439368260977, 360582439195768000, 360582438823044473, 360582438341139135, 360582437858952109, 360582437576893760, 360582437321988932, 360582436965535585]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 70650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 70600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587218293085812, 360587250505907920⟩, ⟨(-341810361203381376), (-340272692338393014)⟩, true⟩

def words06 : List Nat := [360582436608867282, 360582436340586584, 360582436204979669, 360582436237717054, 360582436238656816, 360582436084497445, 360582435784553355, 360582435684779061, 360582435584700381, 360582435621551701]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 70660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 70600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360559447929616471, 360559480151983994⟩, ⟨1620929292305684637, 1622467635793041823⟩, true⟩

def words07 : List Nat := [360582435622444164, 360582435591462813, 360582435637686117, 360582435817359795, 360582435860915829, 360582435904627246, 360582435905528108, 360582435848887989, 360582435592140376, 360582435268506250]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 70600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566818695796707, 360566850927599917⟩, ⟨1099869215715165182, 1101408226162133740⟩, true⟩

def words08 : List Nat := [360582434944549310, 360582434679853942, 360582434287037577, 360582433794254278, 360582433301321428, 360582432726660039, 360582432357189993, 360582432187651708, 360582432018008883, 360582431748453817]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 70680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 70600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574239653733968, 360574271895004666⟩, ⟨575244933318650543, 576784613069558941⟩, true⟩

def words09 : List Nat := [360582431528856421, 360582431468598740, 360582431408062560, 360582431343401119, 360582431219763809, 360582430925796482, 360582430631651211, 360582430369219805, 360582430207546408, 360582430093209328]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 70690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 70600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 70600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk706B
