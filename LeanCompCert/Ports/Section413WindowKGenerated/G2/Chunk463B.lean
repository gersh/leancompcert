import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk463A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk463B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk463A

def state06 : KState := ⟨⟨360582705988779254, 360582719388496676⟩, ⟨14184045206646999, 14603830527195149⟩, true⟩

def words05 : List Nat := [360583032773831896, 360583033013999803, 360583033021690298, 360583033337178941, 360583033458616192, 360583033580216449, 360583034059120098, 360583034403344599, 360583034403918499, 360583034397783286]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 46350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 46300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360605967212005858, 360605980617732711⟩, ⟨(-1064399534441903871), (-1063979470494193991)⟩, true⟩

def words06 : List Nat := [360583034391512058, 360583034314859160, 360583034725622102, 360583035136489148, 360583035137079585, 360583035098457278, 360583034781883684, 360583034813824717, 360583035189632015, 360583035685113312]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 46360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 46300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579651002377577, 360579664414162127⟩, ⟨156040775800335244, 156461120673225442⟩, true⟩

def words07 : List Nat := [360583035820514028, 360583035955975034, 360583036426823733, 360583037194041522, 360583037615467191, 360583038036974933, 360583038223836715, 360583038224473117, 360583037947162498, 360583037875151201]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 46370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 46300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588567978318281, 360588581396102643⟩, ⟨(-257483873351514619), (-257063250176451249)⟩, true⟩

def words08 : List Nat := [360583038193825385, 360583038602150050, 360583038778441577, 360583038954798021, 360583039013611585, 360583039309212938, 360583039676644777, 360583040044179161, 360583040044933498, 360583040165041092]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 46380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 46300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360605665074736713, 360605678498530475⟩, ⟨(-1050812697799003164), (-1050391795818071740)⟩, true⟩

def words09 : List Nat := [360583040499540369, 360583040834210981, 360583041326293442, 360583041354715706, 360583041355308046, 360583040989510077, 360583040623597787, 360583040255242088, 360583040743650020, 360583041232182378]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 46390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 46300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 46300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk463B
