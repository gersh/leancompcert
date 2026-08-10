import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk960A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk960B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk960A

def state06 : KState := ⟨⟨360598907852502543, 360598968814696775⟩, ⟨(-1609063327889432199), (-1605109064270896559)⟩, true⟩

def words05 : List Nat := [360582257921402680, 360582258001762643, 360582258190276446, 360582258463341166, 360582258708343421, 360582258953568032, 360582259128423072, 360582259195347342, 360582259370423026, 360582259545958464]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 96050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 96000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589020353144216, 360589081328479977⟩, ⟨(-659280388194341524), (-655324862135864832)⟩, true⟩

def words06 : List Nat := [360582259718412210, 360582259821610646, 360582259826851342, 360582259832238217, 360582259833403986, 360582259845117060, 360582259916577482, 360582259988325529, 360582260000267514, 360582260072719802]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 96060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 96000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360613919123939711, 360613980112414142⟩, ⟨(-3051467557095064397), (-3047510768738989037)⟩, true⟩

def words07 : List Nat := [360582260196101905, 360582260319889211, 360582260532932922, 360582260734624842, 360582260831953644, 360582260929352412, 360582261084630308, 360582261307935148, 360582261639190395, 360582261970755136]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 96070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 96000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592446863299598, 360592507865060849⟩, ⟨(-988339124731962645), (-984381059711754967)⟩, true⟩

def words08 : List Nat := [360582262247560537, 360582262527048455, 360582262793026289, 360582263059418841, 360582263256018704, 360582263368206523, 360582263425699397, 360582263483343361, 360582263498191488, 360582263606392382]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 96080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 96000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582511746742825, 360582572761627666⟩, ⟨(-33572203555763478), (-29612877424467128)⟩, true⟩

def words09 : List Nat := [360582263804193175, 360582264002257151, 360582264145566069, 360582264238727463, 360582264304040189, 360582264369766154, 360582264543358987, 360582264609246762, 360582264613694784, 360582264618346905]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 96090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 96000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 96000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk960B
