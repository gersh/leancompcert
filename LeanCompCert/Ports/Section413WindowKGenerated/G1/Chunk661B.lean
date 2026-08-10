import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk661A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk661B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk661A

def state06 : KState := ⟨⟨362467267159988063, 362467331834304354⟩, ⟨1199963746897843486, 1202853713924728922⟩, true⟩

def words05 : List Nat := [371285513650908608, 371285513680230318, 371285513708830477, 371285513711102382, 371285513578195179, 371285513487996173, 371285513396688705, 371285513360380784, 371285513087713899, 371285512815470085]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 66150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 66100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485642470524409, 362485707165023567⟩, ⟨(-15808306562514392), (-12917004132756866)⟩, true⟩

def words06 : List Nat := [371285512542200747, 371285512498136156, 371285512386116248, 371285512435739900, 371285512437496996, 371285512416979771, 371285512091437744, 371285511970651450, 371285511953305908, 371285511958601831]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 66160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 66100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500161038627862, 362500225753678538⟩, ⟨(-976595158006860477), (-973702495580156707)⟩, true⟩

def words07 : List Nat := [371285511960320090, 371285511916979663, 371285512055123342, 371285512140908225, 371285512293117226, 371285512446233567, 371285512588635805, 371285512590933153, 371285512809000233, 371285513034082580]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 66170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 66100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479191972382093, 362479256707500802⟩, ⟨411256040853296186, 414150031489439994⟩, true⟩

def words08 : List Nat := [371285513387858042, 371285513438185094, 371285513486665655, 371285513535918470, 371285513591426407, 371285513593935855, 371285513586743782, 371285513640250837, 371285513693101275, 371285513695436887]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 66180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 66100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502084722730334, 362502149478315486⟩, ⟨(-1104100865125136515), (-1101205519715743573)⟩, true⟩

def words09 : List Nat := [371285513735933966, 371285513872203533, 371285514186021404, 371285514253829560, 371285514283459930, 371285514313772302, 371285514538330411, 371285514698451006, 371285514951289761, 371285515205121490]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 66190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 66100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 66100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk661B
