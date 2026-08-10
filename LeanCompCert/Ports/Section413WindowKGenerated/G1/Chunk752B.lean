import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk752A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk752B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk752A

def state06 : KState := ⟨⟨362479920818594909, 362480005353056958⟩, ⟨389082631525168467, 393378994955256815⟩, true⟩

def words05 : List Nat := [371285232739654325, 371285232710157095, 371285232823187754, 371285232825777638, 371285232754744611, 371285232652697903, 371285232549612052, 371285232489901401, 371285232352853931, 371285232286287828]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477240993463517, 362477325551299528⟩, ⟨590744486391120600, 595042609060099398⟩, true⟩

def words06 : List Nat := [371285232218773214, 371285232152043251, 371285231929697508, 371285231867816020, 371285231804561181, 371285231795854512, 371285231551295017, 371285231306752133, 371285231061182976, 371285230993162955]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472445075899210, 362472529657117460⟩, ⟨951758430981317982, 956058313748254480⟩, true⟩

def words07 : List Nat := [371285230889924376, 371285230861481162, 371285230832153762, 371285230768557067, 371285230493637200, 371285230273846545, 371285230052705580, 371285230008756700, 371285229853613088, 371285229687852692]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481901709871046, 362481986314249878⟩, ⟨239842806885357826, 244144433300988580⟩, true⟩

def words08 : List Nat := [371285229520908537, 371285229514295342, 371285229437291323, 371285229458956314, 371285229461015639, 371285229434469608, 371285229171996550, 371285229068132250, 371285229032158535, 371285229034840940]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467661401146484, 362467746029148897⟩, ⟨1312108313345604647, 1316411718498615011⟩, true⟩

def words09 : List Nat := [371285228993708765, 371285228953553372, 371285228945095262, 371285228947978691, 371285228910584315, 371285228866557381, 371285228821610528, 371285228771452587, 371285228485472277, 371285228256486197]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk752B
