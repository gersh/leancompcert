import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk688A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk688B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk688A

def state06 : KState := ⟨⟨362458073719950298, 362458144000377769⟩, ⟨1875436624146174447, 1878705114699697051⟩, true⟩

def words05 : List Nat := [371285428636476613, 371285428617611193, 371285428597928607, 371285428561545742, 371285428268020858, 371285428030328857, 371285427791397120, 371285427716952798, 371285427361054821, 371285426967480582]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475469775496454, 362475540076987415⟩, ⟨677488810614658772, 680758751708905928⟩, true⟩

def words06 : List Nat := [371285426572881717, 371285426318852090, 371285425976378835, 371285425845438905, 371285425713735287, 371285425548787767, 371285425207226857, 371285425001147985, 371285424793854258, 371285424769185890]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470712824596680, 362470783147600110⟩, ⟨1005117656671060063, 1008389079434547633⟩, true⟩

def words07 : List Nat := [371285424627433342, 371285424444929825, 371285424261480098, 371285424167826077, 371285423993327315, 371285423853744240, 371285423713408687, 371285423573520430, 371285423152138551, 371285422942597708]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362464912515196337, 362464982859161808⟩, ⟨1404739147624204199, 1408012014361454491⟩, true⟩

def words08 : List Nat := [371285422731657720, 371285422731917269, 371285422579964979, 371285422429114055, 371285422277381904, 371285422148396753, 371285421926655054, 371285421755840306, 371285421584213362, 371285421413587145]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497707591921113, 362497777957152413⟩, ⟨(-854679924550078066), (-851405592701906644)⟩, true⟩

def words09 : List Nat := [371285421118505284, 371285421034987070, 371285420972574600, 371285420974978774, 371285420874815334, 371285420741485245, 371285420681578156, 371285420684174110, 371285420834153235, 371285421016139919]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk688B
