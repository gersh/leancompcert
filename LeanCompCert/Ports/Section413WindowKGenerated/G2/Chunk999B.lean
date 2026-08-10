import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk999A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk999B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk999A

def state06 : KState := ⟨⟨360592767428052704, 360592833644039898⟩, ⟨(-1043185822510906948), (-1038716561930651538)⟩, true⟩

def words05 : List Nat := [360582441398566124, 360582441532041796, 360582441647301605, 360582441814095102, 360582441955168091, 360582442096475637, 360582442153510731, 360582442215065395, 360582442320198998, 360582442425845496]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590900956308455, 360590967185975364⟩, ⟨(-856610140822885886), (-852139512748016106)⟩, true⟩

def words06 : List Nat := [360582442631006109, 360582442760033430, 360582442826236290, 360582442892583533, 360582442933393098, 360582443024560780, 360582443112733941, 360582443201173710, 360582443232149587, 360582443318926440]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611937143002740, 360612003386390692⟩, ⟨(-2959663426325233135), (-2955191426490665067)⟩, true⟩

def words07 : List Nat := [360582443505378054, 360582443692268246, 360582443962643468, 360582444264777760, 360582444481639019, 360582444698606053, 360582444949695186, 360582445262231037, 360582445559055045, 360582445856195049]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360599534226098348, 360599600483366430⟩, ⟨(-1719687348721179323), (-1715213961085111597)⟩, true⟩

def words08 : List Nat := [360582446071246479, 360582446186612580, 360582446331601279, 360582446477008762, 360582446596744819, 360582446616918223, 360582446618213717, 360582446588306974, 360582446626683859, 360582446799924070]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582777177127064, 360582843446570171⟩, ⟨(-43992323888266522), (-39517718816227982)⟩, true⟩

def words09 : List Nat := [360582447072620755, 360582447345592232, 360582447568301901, 360582447766256110, 360582447896211805, 360582448026537178, 360582448195081901, 360582448264121837, 360582448269382009]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99990 9 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99900 99 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 99 = 90 + 9 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99900 99 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk999B
