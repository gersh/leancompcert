import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk481A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk481B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk481A

def state06 : KState := ⟨⟨360559917538172111, 360559932044163364⟩, ⟨1088127528653046393, 1088599603282523143⟩, true⟩

def words05 : List Nat := [360582538425305267, 360582538665216122, 360582538665816680, 360582538571154489, 360582538045410944, 360582537412296383, 360582536779013941, 360582536575700555, 360582536325183772, 360582535856523882]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360562746523698321, 360562761035944641⟩, ⟨951996449236000911, 952468825140417881⟩, true⟩

def words06 : List Nat := [360582535387722763, 360582535066308750, 360582535417394167, 360582535808169051, 360582535845576964, 360582535846239875, 360582535452752418, 360582535040106285, 360582534627279734, 360582534106842304]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585134750659869, 360585149269220144⟩, ⟨(-126621120716622190), (-126148440639531412)⟩, true⟩

def words07 : List Nat := [360582533696956176, 360582533072400707, 360582532447744343, 360582532168713044, 360582532169268946, 360582531973360346, 360582531777393077, 360582531314685810, 360582530994473211, 360582531049576726]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360572334779689748, 360572349304494891⟩, ⟨490002909736127953, 490475890723225549⟩, true⟩

def words08 : List Nat := [360582531094727025, 360582531095390145, 360582530710031074, 360582530110214313, 360582529510313651, 360582528671982084, 360582528051644330, 360582527860753861, 360582527669787392, 360582527264460096]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592868719099950, 360592883250162276⟩, ⟨(-499783256800713457), (-499309974249550059)⟩, true⟩

def words09 : List Nat := [360582527053802044, 360582526690953639, 360582526393572841, 360582526394236143, 360582526030107307, 360582525218053567, 360582524405906505, 360582524023130651, 360582524121378476, 360582524336981024]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk481B
