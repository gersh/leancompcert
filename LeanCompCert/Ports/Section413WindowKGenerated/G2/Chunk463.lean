import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk463

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360515997911260902, 360516011274895129⟩, ⟨3103595489417504112, 3104013603006458788⟩, true⟩

def state01 : KState := ⟨⟨360590989422918059, 360591002792546811⟩, ⟨(-368946467940301447), (-368528076775930813)⟩, true⟩

def words00 : List Nat := [360583051157981626, 360583050176095327, 360583049427780905, 360583048884939263, 360583048342087862, 360583047358190298, 360583046288735024, 360583045684691436, 360583045080485988, 360583045113447333]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360550185612154553, 360550198987835265⟩, ⟨1520987100331468525, 1521405771792456213⟩, true⟩

def words01 : List Nat := [360583045114013479, 360583045003819737, 360583045033125490, 360583045439177205, 360583045622879882, 360583045806678166, 360583045807244199, 360583045758265205, 360583045243977169, 360583044535585534]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570353456575227, 360570366838238101⟩, ⟨586643776493597877, 587062725078154313⟩, true⟩

def words02 : List Nat := [360583043827017373, 360583043190585740, 360583042620869066, 360583041816087985, 360583041011239751, 360583039925766215, 360583039195859570, 360583038930916761, 360583038665916004, 360583038168371453]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595316528293921, 360595329915963933⟩, ⟨(-570116897876656689), (-569697670952041725)⟩, true⟩

def words03 : List Nat := [360583037983275291, 360583038071872495, 360583038148763810, 360583038149399443, 360583037761335998, 360583036976786546, 360583036192149275, 360583035872322316, 360583036051009944, 360583036316970557]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572599847573637, 360572613241302884⟩, ⟨482525117654304087, 482944625393127357⟩, true⟩

def words04 : List Nat := [360583036317543324, 360583036359583994, 360583036473437573, 360583036587469085, 360583036588004846, 360583036317842202, 360583035582811724, 360583034486576458, 360583033390266786, 360583032758571345]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk463
