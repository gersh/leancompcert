import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk990A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk990B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk990A

def state06 : KState := ⟨⟨360582700269784423, 360582765253420911⟩, ⟨(-37485193584680865), (-33138565106795747)⟩, true⟩

def words05 : List Nat := [360582429912688221, 360582429979308801, 360582430147519984, 360582430367524020, 360582430521375878, 360582430675452067, 360582430746962163, 360582430748401868, 360582430721535223, 360582430726562644]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360579516908999641, 360579581906187143⟩, ⟨277817801634778580, 282165772543539318⟩, true⟩

def words06 : List Nat := [360582430736635197, 360582430738074974, 360582430646667608, 360582430503592869, 360582430360259358, 360582430191511326, 360582430107225264, 360582430105757750, 360582430104133037, 360582430051665528]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583219547958626, 360583284558758483⟩, ⟨(-89094790905146074), (-84745471352483502)⟩, true⟩

def words07 : List Nat := [360582430024101211, 360582429994504347, 360582429964475207, 360582429965141981, 360582429864114971, 360582429676532013, 360582429488679226, 360582429316954616, 360582429233576243, 360582429243699567]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586425768394183, 360586490792915543⟩, ⟨(-406886718100819272), (-402536038955902206)⟩, true⟩

def words08 : List Nat := [360582429244994492, 360582429196479716, 360582429067213880, 360582429040175726, 360582429012777717, 360582428902368124, 360582428805820280, 360582428658422038, 360582428510740868, 360582428506341022]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360560284652126273, 360560349690228459⟩, ⟨2183629110419243869, 2187981135355298911⟩, true⟩

def words09 : List Nat := [360582428635580529, 360582428765118731, 360582428807156260, 360582428808596519, 360582428749004647, 360582428664029735, 360582428578633996, 360582428554913250, 360582428429543839, 360582428208244154]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk990B
