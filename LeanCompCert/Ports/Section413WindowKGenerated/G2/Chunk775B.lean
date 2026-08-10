import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk775A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk775B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk775A

def state06 : KState := ⟨⟨360588591391729180, 360588630478688106⟩, ⟨(-503206799238268351), (-501159259992556963)⟩, true⟩

def words05 : List Nat := [360582168203793745, 360582168413827281, 360582168495714757, 360582168522451063, 360582168523377612, 360582168508641348, 360582168643601072, 360582168824632085, 360582168908930254, 360582168993405651]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 77550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 77500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602230603946713, 360602269701341806⟩, ⟨(-1561132960152794460), (-1559084611424503768)⟩, true⟩

def words06 : List Nat := [360582169097868683, 360582169297698865, 360582169663147641, 360582170028798928, 360582170252423481, 360582170310340497, 360582170362616238, 360582170415199643, 360582170633399026, 360582170893650472]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 77560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 77500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597817986341913, 360597857094296127⟩, ⟨(-1218807370285504125), (-1216758202436208891)⟩, true⟩

def words07 : List Nat := [360582171029917970, 360582171166293276, 360582171468374151, 360582171899472118, 360582172249649673, 360582172599996703, 360582172848160297, 360582172973968691, 360582173177032252, 360582173380468822]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 77570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 77500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584394229595755, 360584433347989360⟩, ⟨(-177401351253072083), (-175351373463581407)⟩, true⟩

def words08 : List Nat := [360582173579623896, 360582173613252281, 360582173614245594, 360582173521293710, 360582173428158740, 360582173258818102, 360582173286921343, 360582173384591103, 360582173385587630, 360582173403234639]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 77580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 77500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360606820169752442, 360606859298599213⟩, ⟨(-1917535173133140014), (-1915484384231119906)⟩, true⟩

def words09 : List Nat := [360582173599118586, 360582173795322957, 360582174091774966, 360582174363989989, 360582174479449008, 360582174594975629, 360582174706576867, 360582174901341371, 360582175220334904, 360582175539572511]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 77590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 77500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 77500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk775B
