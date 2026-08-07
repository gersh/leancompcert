import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk562

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362466850020609832, 362466896089745445⟩, ⟨1011618834895859416, 1013367833506727558⟩, true⟩

def state01 : KState := ⟨⟨362488382775919886, 362488428862017598⟩, ⟨(-198641507825275561), (-196891555859103483)⟩, true⟩

def words00 : List Nat := [371284927226303440, 371284927168947080, 371284927034516187, 371284926974160810, 371284926913250134, 371284926801870090, 371284926303869331, 371284926123182860, 371284926074814955, 371284926139136684]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 56200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 56200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482391349065711, 362482437452365586⟩, ⟨138215120706921876, 139966039695707376⟩, true⟩

def words01 : List Nat := [371284926177787448, 371284926217070580, 371284926523254320, 371284926672851221, 371284926917859626, 371284927163600128, 371284927345343602, 371284927347236702, 371284927107270868, 371284927065309302]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 56210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 56200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362461479503191285, 362461525623347935⟩, ⟨1313970392951236717, 1315722259716442907⟩, true⟩

def words02 : List Nat := [371284927076008433, 371284927077901730, 371284926711524080, 371284926345664145, 371284925979038344, 371284925668885065, 371284925199965684, 371284924987186358, 371284924773793411, 371284924560920698]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 56220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 56200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486875340879639, 362486921478216533⟩, ⟨(-114231135374672477), (-112478302482441181)⟩, true⟩

def words03 : List Nat := [371284924146107468, 371284923804797675, 371284923462466467, 371284923391336184, 371284922963499102, 371284922453815672, 371284921943392536, 371284921749788031, 371284921506241863, 371284921543960698]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 56230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 56200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362465273609555594, 362465319763963673⟩, ⟨1100687095915954712, 1102440888979137832⟩, true⟩

def words04 : List Nat := [371284921578764800, 371284921580659295, 371284921240488149, 371284921063364219, 371284920885354079, 371284920724739758, 371284920142527584, 371284919560978812, 371284918978663871, 371284918713101080]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 56240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 56200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk562
