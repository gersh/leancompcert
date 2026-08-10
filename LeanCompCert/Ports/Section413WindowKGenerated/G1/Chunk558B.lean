import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk558A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk558B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk558A

def state06 : KState := ⟨⟨362495658452462488, 362495703944007201⟩, ⟨(-603752830858093614), (-602036194844870830)⟩, true⟩

def words05 : List Nat := [371284925219199287, 371284925346337002, 371284925570056890, 371284925671628051, 371284925870328329, 371284926069765303, 371284926256691599, 371284926258584179, 371284926351342838, 371284926546630769]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480956100681909, 362481001608949442⟩, ⟨217661168138729309, 219378738377439267⟩, true⟩

def words06 : List Nat := [371284926953996167, 371284927111409293, 371284927266254730, 371284927421730866, 371284927674404135, 371284927767451700, 371284927931609670, 371284928096484849, 371284928199777809, 371284928201725126]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362514217042018060, 362514262567314610⟩, ⟨(-1640740640119008970), (-1639022118386064976)⟩, true⟩

def words07 : List Nat := [371284928382381155, 371284928634330590, 371284929144473157, 371284929471522639, 371284929733831316, 371284929996697089, 371284930536306347, 371284930934503915, 371284931460690235, 371284931987718933]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489921898791581, 362489967441084618⟩, ⟨(-283103794020554343), (-281384322437318993)⟩, true⟩

def words08 : List Nat := [371284932452466106, 371284932491140755, 371284932670572497, 371284932850949241, 371284933128362458, 371284933130243501, 371284932981306583, 371284932825089873, 371284932829459168, 371284932921708738]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475293733947012, 362475339293145623⟩, ⟨534569266773474250, 536289683294624566⟩, true⟩

def words09 : List Nat := [371284933177605570, 371284933434232406, 371284933688072760, 371284933689954007, 371284933517400263, 371284933360661364, 371284933363560816, 371284933365446213, 371284933195817365, 371284933026299373]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk558B
