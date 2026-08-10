import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk598A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk598B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk598A

def state06 : KState := ⟨⟨360548632393174548, 360548655201438258⟩, ⟨2005904470690995917, 2006826836654738825⟩, true⟩

def words05 : List Nat := [360582181028134272, 360582181484497002, 360582181779709458, 360582181796986420, 360582181797686854, 360582181743674703, 360582181689431163, 360582181517688634, 360582181100379991, 360582180541175224]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 59850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 59800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580724840202833, 360580747656368768⟩, ⟨84767983640128462, 85690822670738840⟩, true⟩

def words06 : List Nat := [360582179981799348, 360582179589254771, 360582179513222859, 360582179615324031, 360582179616099614, 360582179477135884, 360582179182658634, 360582179106982407, 360582179031056821, 360582178937856504]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 59860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 59800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594627495577508, 360594650319727552⟩, ⟨(-747762648520046633), (-746839331441342455)⟩, true⟩

def words07 : List Nat := [360582178914709285, 360582178679260098, 360582178443662810, 360582178256992600, 360582178257694200, 360582178189721901, 360582178121667238, 360582177913851000, 360582178052048283, 360582178261287624]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 59870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 59800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595956210614567, 360595979042645096⟩, ⟨(-827374462669666090), (-826450673668176978)⟩, true⟩

def words08 : List Nat := [360582178693159038, 360582178925983468, 360582179018334957, 360582179110780632, 360582179111494459, 360582178952776404, 360582179189041465, 360582179447152621, 360582179564842187, 360582179796119439]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 59880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 59800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360591054366742750, 360591077206692759⟩, ⟨(-533826453096212443), (-532902189759453557)⟩, true⟩

def words09 : List Nat := [360582179971580078, 360582180147293741, 360582180523856674, 360582180622914013, 360582180623698862, 360582180448397864, 360582180308839609, 360582180525895729, 360582180675110608, 360582180824499483]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 59890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 59800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 59800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk598B
