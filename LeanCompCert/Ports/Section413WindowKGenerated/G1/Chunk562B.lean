import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk562A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk562B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk562A

def state06 : KState := ⟨⟨362456425576187950, 362456471747668644⟩, ⟨1598502684619128839, 1600257438102250255⟩, true⟩

def words05 : List Nat := [371284918365973092, 371284918228919186, 371284918091215598, 371284917919563809, 371284917464447289, 371284917106415336, 371284916747387548, 371284916652247312, 371284916215563476, 371284915712085677]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489609064969308, 362489655253404575⟩, ⟨(-268542381769512319), (-266786674334773937)⟩, true⟩

def words06 : List Nat := [371284915207799763, 371284914990559374, 371284914614711404, 371284914555346744, 371284914495379626, 371284914366607514, 371284913975121112, 371284913900278300, 371284914062983301, 371284914149206413]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490074594955923, 362490120800700213⟩, ⟨(-294737226061713129), (-292980544562244337)⟩, true⟩

def words07 : List Nat := [371284914234809240, 371284914321072745, 371284914537025014, 371284914620641854, 371284914797167753, 371284914974407393, 371284915119482973, 371284915121382412, 371284915031689375, 371284915126590616]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467536161454324, 362467582384074941⟩, ⟨973880796904726994, 975638428292045452⟩, true⟩

def words08 : List Nat := [371284915447621113, 371284915449516715, 371284915387362183, 371284915326800815, 371284915298977702, 371284915301086773, 371284915197714574, 371284915052939620, 371284914907505369, 371284914742012267]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504277986855534, 362504324226577718⟩, ⟨(-1094502536616584070), (-1092743942493731558)⟩, true⟩

def words09 : List Nat := [371284914435392402, 371284914419320870, 371284914620804872, 371284914622733882, 371284914580797964, 371284914490401598, 371284914540538273, 371284914572162029, 371284914918202750, 371284915265058496]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk562B
