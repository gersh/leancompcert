import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk805A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk805B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk805A

def state06 : KState := ⟨⟨360571982127968720, 360572024422468196⟩, ⟨813207442062265169, 815508601543714577⟩, true⟩

def words05 : List Nat := [360582147487935324, 360582147697879283, 360582147791452972, 360582147792605483, 360582147732297919, 360582147633900454, 360582147589327176, 360582147590480091, 360582147543475145, 360582147419011688]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575990586056648, 360576032891455088⟩, ⟨490232896188356928, 492534933743484294⟩, true⟩

def words06 : List Nat := [360582147294291675, 360582147229275613, 360582147230226313, 360582147181116627, 360582147131911488, 360582146938091287, 360582146590285608, 360582146396670732, 360582146202711327, 360582146022071242]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562740945824577, 360562783262198419⟩, ⟨1557856894630179479, 1560159816527256387⟩, true⟩

def words07 : List Nat := [360582145947225977, 360582145785887022, 360582145624331337, 360582145656479688, 360582145657452278, 360582145623085712, 360582145588622139, 360582145434829413, 360582145127079441, 360582144888117100]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563512796795443, 360563555124023475⟩, ⟨1495647149200788360, 1497950945782852528⟩, true⟩

def words08 : List Nat := [360582144648774079, 360582144519474822, 360582144293946049, 360582143991634269, 360582143689122102, 360582143319446678, 360582143081810505, 360582142890023611, 360582142698115918, 360582142429468107]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569166153448870, 360569208491584134⟩, ⟨1039935666054082636, 1042240341701127726⟩, true⟩

def words09 : List Nat := [360582142199780001, 360582141919179232, 360582141638245056, 360582141476304892, 360582141211236106, 360582140819463357, 360582140427488402, 360582139985644026, 360582139672427993, 360582139513193330]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk805B
