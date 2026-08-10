import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk979A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk979B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk979A

def state06 : KState := ⟨⟨360578032003857601, 360578095497591194⟩, ⟨419572202673891147, 423772059285138879⟩, true⟩

def words05 : List Nat := [360582421395275639, 360582421490905072, 360582421528146646, 360582421577194495, 360582421578398899, 360582421536376793, 360582421499883474, 360582421509399286, 360582421510666741, 360582421467979977]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360619498587622759, 360619562094781615⟩, ⟨(-3642711578102215227), (-3638510406287388859)⟩, true⟩

def words06 : List Nat := [360582421484958730, 360582421612794248, 360582421822465135, 360582422032407649, 360582422143312338, 360582422272290281, 360582422505117981, 360582422738366572, 360582423067011656, 360582423447566752]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607145954475521, 360607209475197466⟩, ⟨(-2432419398487068607), (-2428216897828707017)⟩, true⟩

def words07 : List Nat := [360582423756142284, 360582424064888250, 360582424477454942, 360582424943038465, 360582425381871037, 360582425820926338, 360582426181464355, 360582426438303807, 360582426692413793, 360582426946974355]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608535195600165, 360608598729722530⟩, ⟨(-2568607540969244542), (-2564403727270625416)⟩, true⟩

def words08 : List Nat := [360582427231903210, 360582427413259850, 360582427529421645, 360582427645720588, 360582427735442319, 360582427906709683, 360582428181621054, 360582428456813396, 360582428672862626, 360582428941402474]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360605428835387083, 360605492382961424⟩, ⟨(-2264215569442159718), (-2260010437518156904)⟩, true⟩

def words09 : List Nat := [360582429224857159, 360582429508737017, 360582429789740745, 360582430039970707, 360582430199203065, 360582430358542552, 360582430560096623, 360582430813984209, 360582431050464857, 360582431287283644]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk979B
