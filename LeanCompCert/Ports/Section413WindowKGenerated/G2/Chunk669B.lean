import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk669A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk669B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk669A

def state06 : KState := ⟨⟨360579554241407188, 360579583037169286⟩, ⟨222190752611953445, 223493215119387921⟩, true⟩

def words05 : List Nat := [360582920265953442, 360582920438436563, 360582920601108503, 360582920875890747, 360582920996896320, 360582921118040676, 360582921118888078, 360582921069944758, 360582920798219713, 360582920749461989]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584303381841595, 360584332186513793⟩, ⟨(-95848264712005737), (-94545205539501511)⟩, true⟩

def words06 : List Nat := [360582920771125819, 360582920849427987, 360582920850276186, 360582920750799508, 360582920651171896, 360582920444093352, 360582920432145985, 360582920516736359, 360582920517600975, 360582920452994218]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360609610816505272, 360609639630099884⟩, ⟨(-1790816649190392223), (-1789512992439646081)⟩, true⟩

def words07 : List Nat := [360582920653102689, 360582920853482474, 360582921276107759, 360582921476403080, 360582921489899547, 360582921503488368, 360582921739382267, 360582922105059684, 360582922504717040, 360582922904574144]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583127278631982, 360583156101238478⟩, ⟨(-16951815898220035), (-15647555488643561)⟩, true⟩

def words08 : List Nat := [360582923180734102, 360582923287661386, 360582923384839270, 360582923482278024, 360582923523448031, 360582923524393234, 360582923343203024, 360582923047088825, 360582922750806134, 360582922524258158]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360553378903560884, 360553407735059773⟩, ⟨1976145843219160825, 1977450699374235291⟩, true⟩

def words09 : List Nat := [360582922663316184, 360582922802550934, 360582922808397423, 360582922837983478, 360582922838774635, 360582922812504044, 360582922785962576, 360582922660104778, 360582922364139511, 360582921924602673]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk669B
