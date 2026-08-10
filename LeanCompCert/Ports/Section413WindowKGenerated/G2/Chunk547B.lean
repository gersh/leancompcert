import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk547A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk547B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk547A

def state06 : KState := ⟨⟨360583683540863580, 360583702492351330⟩, ⟨(-108106347404254708), (-107405169218107298)⟩, true⟩

def words05 : List Nat := [360581740233185636, 360581740523598120, 360581740647322473, 360581740780256069, 360581740780893177, 360581740774546657, 360581740871945776, 360581741075058943, 360581741111555446, 360581741148160791]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588036900724264, 360588055859403307⟩, ⟨(-346496676319967210), (-345795104301983596)⟩, true⟩

def words06 : List Nat := [360581741176413196, 360581741372607166, 360581741724576586, 360581742076678115, 360581742143736905, 360581742144498194, 360581742098210595, 360581742241964224, 360581742272632107, 360581742388692494]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591758715918527, 360591777681843473⟩, ⟨(-550359615525408561), (-549657646613877003)⟩, true⟩

def words07 : List Nat := [360581742389370721, 360581742339012963, 360581742570043602, 360581743087803523, 360581743372567626, 360581743657434117, 360581743734806227, 360581743735567723, 360581743769932271, 360581743953970418]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360618083917923340, 360618102891022312⟩, ⟨(-1992550690741563940), (-1991848328800577574)⟩, true⟩

def words08 : List Nat := [360581744318253385, 360581744861249240, 360581745235176265, 360581745609165888, 360581745899315652, 360581746404623818, 360581747242169223, 360581748079829950, 360581748659009472, 360581749323304976]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360630716280592044, 360630735260879188⟩, ⟨(-2684875641004273193), (-2684172885187911095)⟩, true⟩

def words09 : List Nat := [360581749882089308, 360581750441078629, 360581751257045454, 360581751741028966, 360581751946235429, 360581752151505421, 360581752546249953, 360581753108610220, 360581754003060901, 360581754897652461]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk547B
