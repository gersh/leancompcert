import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk433A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk433B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk433A

def state06 : KState := ⟨⟨360564940570693262, 360564952227974218⟩, ⟨789275775911267776, 789617364006635134⟩, true⟩

def words05 : List Nat := [360583164853315420, 360583165238812932, 360583165357606631, 360583165358198174, 360583165128458775, 360583164437502088, 360583163746404090, 360583163457103990, 360583163379925590, 360583162960538947]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598100760021976, 360598112422886577⟩, ⟨(-648635411207113802), (-648293580978092392)⟩, true⟩

def words06 : List Nat := [360583162541037780, 360583162906701777, 360583163684516539, 360583164462408981, 360583164715795856, 360583164716387484, 360583164439756788, 360583164339783393, 360583164449459425, 360583164794725408]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360573550817826170, 360573562486334243⟩, ⟨416220604136364300, 416562679150464336⟩, true⟩

def words07 : List Nat := [360583164808412955, 360583164822169692, 360583164916577196, 360583165277623092, 360583165477367175, 360583165677197992, 360583165677726203, 360583165556468716, 360583165350614645, 360583165129929229]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360562968242457467, 360562979916538031⟩, ⟨875233142293198495, 875575459070452163⟩, true⟩

def words08 : List Nat := [360583164909054254, 360583164653390025, 360583163985732923, 360583163050559167, 360583162115325972, 360583161043466983, 360583160379525346, 360583160047170009, 360583159714770714, 360583159115871298]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360613069030092076, 360613080709767971⟩, ⟨(-1298979397743499089), (-1298636838156877381)⟩, true⟩

def words09 : List Nat := [360583158717033230, 360583158783420470, 360583158834799942, 360583158835394710, 360583158730284535, 360583158094140966, 360583157457912162, 360583157511398477, 360583158201351840, 360583158891419157]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk433B
