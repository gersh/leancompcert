import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk216A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk216B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk216A

def state06 : KState := ⟨⟨360625901683899185, 360625904426327861⟩, ⟨(-994026944723780702), (-993986751879016414)⟩, true⟩

def words05 : List Nat := [360580001928180872, 360580002101553458, 360580003620684081, 360580006228969258, 360580007822270472, 360580009415469999, 360580009939351047, 360580011875253480, 360580013994250902, 360580016113143843]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360629928459374336, 360629931204433113⟩, ⟨(-1081417073952057550), (-1081376824126193254)⟩, true⟩

def words06 : List Nat := [360580020355455391, 360580022478298545, 360580023247141662, 360580024015941840, 360580024016179939, 360580024039211302, 360580026162484983, 360580028285615972, 360580029181800996, 360580031484801985]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360634160855535217, 360634163603237082⟩, ⟨(-1173110629707589655), (-1173070322593000555)⟩, true⟩

def words07 : List Nat := [360580034412500640, 360580037340017741, 360580042388638365, 360580045319090065, 360580046198792368, 360580047078434520, 360580049351887736, 360580052697112584, 360580055193233872, 360580057689183626]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360633663687920912, 360633666438289016⟩, ⟨(-1162635601253537410), (-1162595236321880628)⟩, true⟩

def words08 : List Nat := [360580058558769372, 360580058559049384, 360580060124144643, 360580061966567938, 360580063269388435, 360580064647069334, 360580064958721916, 360580065270376376, 360580065919925865, 360580068391342270]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360548685253102320, 360548688006111291⟩, ⟨681117775273396217, 681158197498605257⟩, true⟩

def words09 : List Nat := [360580072510157890, 360580076628649967, 360580079114561786, 360580079487042151, 360580079487276602, 360580079322045445, 360580079617424943, 360580079617705576, 360580079231102942, 360580077784797863]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk216B
