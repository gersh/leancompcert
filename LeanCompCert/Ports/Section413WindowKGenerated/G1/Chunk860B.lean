import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk860A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk860B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk860A

def state06 : KState := ⟨⟨362481686859607282, 362481798544538231⟩, ⟨290108316797002905, 296598160671057283⟩, true⟩

def words05 : List Nat := [371285246100230133, 371285245985345793, 371285245868957873, 371285245823041623, 371285245638092752, 371285245432163182, 371285245224991603, 371285245133454514, 371285244992584190, 371285244955886954]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475910691584126, 362476022403487253⟩, ⟨787188704165414455, 793680869402097037⟩, true⟩

def words06 : List Nat := [371285244918077429, 371285244881141006, 371285244687132885, 371285244612430876, 371285244536221570, 371285244467792862, 371285244252676393, 371285244038867317, 371285243823871920, 371285243745062740]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362461306174418709, 362461417913345863⟩, ⟨2044305585346777631, 2050800076676072219⟩, true⟩

def words07 : List Nat := [371285243639962028, 371285243601043424, 371285243561037829, 371285243519312136, 371285243296873265, 371285243082305339, 371285242866185780, 371285242785805757, 371285242537044672, 371285242263678996]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478978356633566, 362479090122349656⟩, ⟨523035585751626547, 529532383209929029⟩, true⟩

def words08 : List Nat := [371285241988942539, 371285241825289080, 371285241592943564, 371285241496552862, 371285241399281160, 371285241281351964, 371285241117975593, 371285241070220876, 371285241035538014, 371285241038637378]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467697212753818, 362467809005751080⟩, ⟨1494316280439112803, 1500815426670857757⟩, true⟩

def words09 : List Nat := [371285240969428396, 371285240901302281, 371285240832022215, 371285240815327144, 371285240729934456, 371285240675822117, 371285240620675664, 371285240539655121, 371285240277939741, 371285240079231578]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk860B
