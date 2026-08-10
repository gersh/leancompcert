import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk744A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk744B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk744A

def state06 : KState := ⟨⟨362477681088196059, 362477763766713322⟩, ⟨553622928310996529, 557780354123490489⟩, true⟩

def words05 : List Nat := [371285254590655136, 371285254547113569, 371285254636326840, 371285254682753867, 371285254783419438, 371285254885087345, 371285254985024154, 371285254987585156, 371285254870803171, 371285254773349416]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 74450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 74400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478179962458828, 362478262663798243⟩, ⟨516473916542978556, 520633041810265486⟩, true⟩

def words06 : List Nat := [371285254707224836, 371285254709787636, 371285254540433896, 371285254372285721, 371285254203111754, 371285254081126244, 371285253894524162, 371285253879729161, 371285253864092945, 371285253842015113]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 74460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 74400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490673185081032, 362490755909621312⟩, ⟨(-413947372088896707), (-409786518940509891)⟩, true⟩

def words07 : List Nat := [371285253836080201, 371285253925374546, 371285254088829160, 371285254091394116, 371285254061199426, 371285254000240850, 371285253944708230, 371285253947530750, 371285253939425865, 371285254016266759]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 74470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 74400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476619625582034, 362476702373201680⟩, ⟨632770884514918261, 636933456735150889⟩, true⟩

def words08 : List Nat := [371285254036352360, 371285254038914024, 371285253837793680, 371285253801209373, 371285253778943296, 371285253781504971, 371285253558920215, 371285253300688306, 371285253041397865, 371285252963304180]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 74480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 74400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471714601349436, 362471797372018900⟩, ⟨998249060384828076, 1002413349699850492⟩, true⟩

def words09 : List Nat := [371285252896752660, 371285252946025002, 371285252992026777, 371285252994640756, 371285252926010333, 371285252901306413, 371285252932318578, 371285252934880954, 371285252762517876, 371285252584766549]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 74490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 74400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 74400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk744B
