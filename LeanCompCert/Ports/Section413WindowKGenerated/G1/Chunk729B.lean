import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk729A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk729B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk729A

def state06 : KState := ⟨⟨362487336151623174, 362487415407021899⟩, ⟨(-158969998235509648), (-155064900211443322)⟩, true⟩

def words05 : List Nat := [371285289952047454, 371285289865800427, 371285289877246189, 371285289911940685, 371285290002625896, 371285290094263219, 371285290187847644, 371285290190353739, 371285290062586582, 371285290094865933]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 72950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 72900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472480319582417, 362472559597317813⟩, ⟨924973550367436789, 928880278191477201⟩, true⟩

def words06 : List Nat := [371285290201583572, 371285290204089736, 371285290070869341, 371285289890953352, 371285289710093799, 371285289587317300, 371285289369384565, 371285289319301619, 371285289268312508, 371285289216040459]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 72960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 72900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497703068960152, 362497782369313020⟩, ⟨(-915626350631056023), (-911717972294438529)⟩, true⟩

def words07 : List Nat := [371285289043293445, 371285289028403399, 371285289181976695, 371285289222000305, 371285289223976131, 371285289219549801, 371285289394524678, 371285289483678597, 371285289656567242, 371285289830538621]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 72970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 72900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483781500382377, 362483860823388069⟩, ⟨100442682490536980, 104352714147336220⟩, true⟩

def words08 : List Nat := [371285289980102378, 371285290021720886, 371285290216104296, 371285290411803944, 371285290614338202, 371285290616845264, 371285290569356364, 371285290523165690, 371285290505583810, 371285290508470236]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 72980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 72900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482496986678591, 362482576332295156⟩, ⟨194232710115271357, 198144392251839811⟩, true⟩

def words09 : List Nat := [371285290629396117, 371285290770960566, 371285290897375558, 371285290899882806, 371285290776129302, 371285290691443442, 371285290705214468, 371285290707734426, 371285290673377356, 371285290639038332]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 72990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 72900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 72900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk729B
