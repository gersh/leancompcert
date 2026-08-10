import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk639A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk639B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk639A

def state06 : KState := ⟨⟨360610174312349627, 360610200489580074⟩, ⟨(-1753244230508384788), (-1752113209206844378)⟩, true⟩

def words05 : List Nat := [360582801749649226, 360582802191628623, 360582802779433118, 360582803595366570, 360582804349108977, 360582805102974742, 360582805733731254, 360582806169430095, 360582806598473925, 360582807027795443]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360605101553967338, 360605127739660884⟩, ⟨(-1428804699630888808), (-1427673136985968526)⟩, true⟩

def words06 : List Nat := [360582807651541544, 360582808032252354, 360582808249412109, 360582808466653803, 360582808524180519, 360582808771656044, 360582809183493782, 360582809595490694, 360582809884470177, 360582810234275851]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606489703528234, 360606515897728578⟩, ⟨(-1517752018880864303), (-1516619912014190245)⟩, true⟩

def words07 : List Nat := [360582810572440844, 360582810910866140, 360582811062887293, 360582811083585552, 360582811084416188, 360582810894001909, 360582810756267639, 360582810931736890, 360582811302970303, 360582811674412060]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601810619917702, 360601836822694435⟩, ⟨(-1218499350670093134), (-1217366695045822254)⟩, true⟩

def words08 : List Nat := [360582811924097699, 360582811930843882, 360582812130803489, 360582812331021850, 360582812430653256, 360582812574373007, 360582812575194201, 360582812491260571, 360582812494496223, 360582812792830145]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360604511481809492, 360604537693059095⟩, ⟨(-1391293761420655910), (-1390160563574128470)⟩, true⟩

def words09 : List Nat := [360582813275016281, 360582813757361554, 360582814104721956, 360582814462000952, 360582814757311098, 360582815052850463, 360582815592103052, 360582816093107235, 360582816433320496, 360582816773642616]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk639B
