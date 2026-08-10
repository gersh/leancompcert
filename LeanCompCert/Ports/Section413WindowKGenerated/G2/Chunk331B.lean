import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk331A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk331B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk331A

def state06 : KState := ⟨⟨360527488051653624, 360527494721298421⟩, ⟨1781502823248794050, 1781652364525197320⟩, true⟩

def words05 : List Nat := [360581229510702531, 360581229573253395, 360581229573647932, 360581229082625994, 360581228546675234, 360581227556625486, 360581226566501175, 360581226221513463, 360581225302719197, 360581223682834163]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360603242637050846, 360603249310874245⟩, ⟨(-730881940861396507), (-730732261001990561)⟩, true⟩

def words06 : List Nat := [360581222062946844, 360581221350875848, 360581221103763186, 360581221112014621, 360581221112429436, 360581220196901599, 360581219644134983, 360581219388854612, 360581219396004893, 360581220060595327]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360595621089675869, 360595627767723967⟩, ⟨(-478111233301330950), (-477961413288248646)⟩, true⟩

def words07 : List Nat := [360581220269150702, 360581220477741837, 360581220655400770, 360581221454402801, 360581222021018543, 360581222587677302, 360581222698646439, 360581222699089533, 360581222661324750, 360581223095975429]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565504337488593, 360565511019705973⟩, ⟨521423940047259912, 521573898418535812⟩, true⟩

def words08 : List Nat := [360581224436811598, 360581225206913051, 360581225514597295, 360581225822308581, 360581225898589799, 360581226430970143, 360581226476494059, 360581226522091392, 360581226522488801, 360581225810257903]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360658802101107166, 360658808787505867⟩, ⟨(-2575680518367246228), (-2575530421196829558)⟩, true⟩

def words09 : List Nat := [360581225769552219, 360581226202420004, 360581227031168284, 360581227889565647, 360581227974021293, 360581228058506685, 360581228800582077, 360581230232478592, 360581232569540631, 360581234906562618]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk331B
