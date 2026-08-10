import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk677A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk677B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk677A

def state06 : KState := ⟨⟨360588602818545099, 360588632334238083⟩, ⟨(-393090209352831972), (-391739251728786326)⟩, true⟩

def words05 : List Nat := [360582853250808299, 360582853050133920, 360582852849188514, 360582852643475722, 360582852343061993, 360582851857375653, 360582851371515920, 360582851103480158, 360582851057371421, 360582851143704756]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 67750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 67700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583975716014464, 360584005240821151⟩, ⟨(-79597589368556216), (-78246014154946016)⟩, true⟩

def words06 : List Nat := [360582851144565466, 360582851121189781, 360582851150470526, 360582851274527183, 360582851343389757, 360582851344347648, 360582851283522442, 360582851056484778, 360582850829273910, 360582850675975496]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 67760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 67700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360559749063752407, 360559778597568468⟩, ⟨1562389469754096417, 1563741655578837939⟩, true⟩

def words07 : List Nat := [360582850676754857, 360582850653399114, 360582850629942685, 360582850439067343, 360582850307998237, 360582850121480978, 360582849964541924, 360582849965499272, 360582849778736871, 360582849439344491]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 67770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 67700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583224222361079, 360583253765228575⟩, ⟨(-28911323065014023), (-27558523689768789)⟩, true⟩

def words08 : List Nat := [360582849099759905, 360582848684845457, 360582848454826281, 360582848442385490, 360582848429870102, 360582848232338729, 360582847817198467, 360582847551596319, 360582847285692905, 360582847243364467]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 67780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 67700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360563234356221628, 360563263908204882⟩, ⟨1326280175730026075, 1327633593106959055⟩, true⟩

def words09 : List Nat := [360582847244217756, 360582847117519320, 360582846990644478, 360582846912831100, 360582846913650472, 360582846740322304, 360582846566901746, 360582846273542019, 360582845812347503, 360582845524622389]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 67790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 67700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 67700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk677B
