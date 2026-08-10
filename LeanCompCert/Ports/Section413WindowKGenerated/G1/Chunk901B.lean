import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk901A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk901B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk901A

def state06 : KState := ⟨⟨362481125044711956, 362481248065498806⟩, ⟨340770693742379906, 348259534941190580⟩, true⟩

def words05 : List Nat := [371285110360981601, 371285110537923590, 371285110690922320, 371285110694067839, 371285110689079602, 371285110699018649, 371285110815083604, 371285110818229975, 371285110788091567, 371285110748894339]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482285295974719, 362482408344895299⟩, ⟨236200272275160531, 243691650155724341⟩, true⟩

def words06 : List Nat := [371285110756731618, 371285110760231356, 371285110859048899, 371285110972251107, 371285111064937181, 371285111068083155, 371285110996589697, 371285110941326059, 371285110921765770, 371285110925023454]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492790196092325, 362492913273673198⟩, ⟨(-711072435514905484), (-703578473192087502)⟩, true⟩

def words07 : List Nat := [371285110897426458, 371285110863872629, 371285110915055695, 371285110974348989, 371285111069377588, 371285111165652438, 371285111260651920, 371285111263819928, 371285111335048259, 371285111425465792]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480176276384947, 362480299382007967⟩, ⟨426499888923021885, 433996380235739279⟩, true⟩

def words08 : List Nat := [371285111543212745, 371285111546359951, 371285111517603469, 371285111480313998, 371285111441797630, 371285111415313543, 371285111357863630, 371285111392967197, 371285111402033782, 371285111405294759]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362500257185441070, 362500380319539543⟩, ⟨(-1384704822928262586), (-1377205763271143676)⟩, true⟩

def words09 : List Nat := [371285111423611889, 371285111496956529, 371285111632736262, 371285111651816570, 371285111654294574, 371285111642802568, 371285111738057924, 371285111787958830, 371285111959367229, 371285112132232627]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk901B
