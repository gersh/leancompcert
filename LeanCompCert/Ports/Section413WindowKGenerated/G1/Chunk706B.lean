import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk706A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk706B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk706A

def state06 : KState := ⟨⟨362472841147009379, 362472915298813316⟩, ⟨871447201243052856, 874985775546777590⟩, true⟩

def words05 : List Nat := [371285299304773109, 371285299359557264, 371285299374111747, 371285299376532051, 371285299124155590, 371285298911995865, 371285298698547138, 371285298685908639, 371285298513761641, 371285298341207129]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485551003524674, 362485625176983461⟩, ⟨(-26656818023975313), (-23116713478923583)⟩, true⟩

def words06 : List Nat := [371285298167606666, 371285298142706379, 371285298088967407, 371285298163919327, 371285298192348031, 371285298194768900, 371285297980926902, 371285297968295373, 371285298066601899, 371285298073737732]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474202953507287, 362474277149062864⟩, ⟨775421379127177320, 778963045362244170⟩, true⟩

def words07 : List Nat := [371285298080513416, 371285298088184469, 371285298245288362, 371285298303325447, 371285298364613819, 371285298426792262, 371285298487827708, 371285298490248731, 371285298284494956, 371285298131594871]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471505864746318, 362471580081881431⟩, ⟨966070019227784949, 969613210812549555⟩, true⟩

def words08 : List Nat := [371285297977319337, 371285297955789077, 371285297693334499, 371285297432018962, 371285297169804551, 371285296952702711, 371285296687696659, 371285296623530803, 371285296558514141, 371285296494539694]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483276087028617, 362483350326041369⟩, ⟨133992269617158455, 137537007844541889⟩, true⟩

def words09 : List Nat := [371285296302148846, 371285296288071615, 371285296339509494, 371285296341942623, 371285296219417384, 371285296066094664, 371285295911780395, 371285295862221514, 371285295711599246, 371285295686831250]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk706B
