import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk937A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk937B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk937A

def state06 : KState := ⟨⟨360554817570610087, 360554875539480481⟩, ⟨2546066426547538696, 2549736579121768282⟩, true⟩

def words05 : List Nat := [360582071509101438, 360582071497515042, 360582071485800317, 360582071386663177, 360582071173839482, 360582070895062142, 360582070615886357, 360582070349341532, 360582070117572933, 360582069828933572]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576116215902807, 360576174197580297⟩, ⟨549047473275025607, 552718826706858885⟩, true⟩

def words06 : List Nat := [360582069539992255, 360582069365152986, 360582069247418981, 360582069243637631, 360582069239766599, 360582069137856549, 360582068945916780, 360582068822002752, 360582068697697807, 360582068607591035]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360558633167317003, 360558691161947866⟩, ⟨2188555991396647664, 2192228559529384344⟩, true⟩

def words07 : List Nat := [360582068545955107, 360582068409392359, 360582068272544890, 360582068226403663, 360582068227549741, 360582068152767813, 360582068077839244, 360582067946014590, 360582067700542980, 360582067452836429]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360572861714044041, 360572919721463442⟩, ⟨854123060383097474, 857796827886883166⟩, true⟩

def words08 : List Nat := [360582067204669166, 360582067051229915, 360582066864188988, 360582066609948168, 360582066355488250, 360582066072819337, 360582065902367807, 360582065845792766, 360582065789085391, 360582065652030527]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580358047690190, 360580416067944067⟩, ⟨150978013952822071, 154652985264198779⟩, true⟩

def words09 : List Nat := [360582065555614219, 360582065542398276, 360582065528802904, 360582065512783987, 360582065444084083, 360582065268965992, 360582065093598686, 360582064935816847, 360582064836597520, 360582064820452215]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk937B
