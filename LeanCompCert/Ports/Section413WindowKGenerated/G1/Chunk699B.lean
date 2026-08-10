import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk699A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk699B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk699A

def state06 : KState := ⟨⟨362483678138429268, 362483750772012974⟩, ⟨108408509543575069, 111840336663587919⟩, true⟩

def words05 : List Nat := [371285350363220939, 371285350211902831, 371285350059588017, 371285350042967592, 371285349932880890, 371285349839181198, 371285349744715640, 371285349649535464, 371285349424454064, 371285349404612511]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 69950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 69900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471081070095339, 362471153724987535⟩, ⟨989786863038320337, 993220181012215673⟩, true⟩

def words06 : List Nat := [371285349532027042, 371285349534422246, 371285349412820157, 371285349292532306, 371285349171381429, 371285349059242340, 371285348878179114, 371285348808665413, 371285348738313538, 371285348668263400]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 69960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 69900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475838053174276, 362475910729716135⟩, ⟨656944497744323542, 660379330654942192⟩, true⟩

def words07 : List Nat := [371285348467030241, 371285348373166452, 371285348362125351, 371285348364521391, 371285348205081762, 371285348014697327, 371285347823327249, 371285347731019777, 371285347548531694, 371285347416350244]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 69970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 69900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467524524830213, 362467597222988681⟩, ⟨1238762936410746124, 1242199282161809054⟩, true⟩

def words08 : List Nat := [371285347283294721, 371285347151387468, 371285346835133583, 371285346691769783, 371285346547160379, 371285346465542657, 371285346213114921, 371285345937840027, 371285345661626593, 371285345462482349]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 69980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 69900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362461541391089162, 362461614110877408⟩, ⟨1657599102212988949, 1661036961939821163⟩, true⟩

def words09 : List Nat := [371285345210528863, 371285345163261682, 371285345115213855, 371285344988058795, 371285344614051863, 371285344303459772, 371285343991654442, 371285343884271045, 371285343546550264, 371285343210333692]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 69990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 69900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 69900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk699B
