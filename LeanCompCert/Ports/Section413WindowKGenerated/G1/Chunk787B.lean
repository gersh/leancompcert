import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk787A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk787B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk787A

def state06 : KState := ⟨⟨362467347818184281, 362467440723814147⟩, ⟨1395780726715984813, 1400721873530791773⟩, true⟩

def words05 : List Nat := [371285226200608997, 371285226215001774, 371285226228424950, 371285226231157332, 371285226093358199, 371285225993074089, 371285225891444402, 371285225857582044, 371285225632577328, 371285225409867103]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 78750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 78700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362467388012320739, 362467480942285616⟩, ⟨1392637232284530781, 1397580295848281535⟩, true⟩

def words06 : List Nat := [371285225185911737, 371285225029699358, 371285224791764768, 371285224698860321, 371285224605082757, 371285224472321510, 371285224123956297, 371285223866215626, 371285223607003487, 371285223487618209]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 78760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 78700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474672557745212, 362474765512493384⟩, ⟨818770899979343989, 823715915846566585⟩, true⟩

def words07 : List Nat := [371285223264460525, 371285223000301131, 371285222735066051, 371285222596033275, 371285222394864510, 371285222208859638, 371285222021934345, 371285221835173245, 371285221543307328, 371285221413938505]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 78770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 78700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474673613827850, 362474766592781068⟩, ⟨818723932192592691, 823670855061845175⟩, true⟩

def words08 : List Nat := [371285221311319507, 371285221314058535, 371285221199797515, 371285221086498224, 371285220972153709, 371285220865386739, 371285220676569841, 371285220649797562, 371285220622131534, 371285220595256787]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 78780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 78700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480448908929815, 362480541912543570⟩, ⟨363663164047795818, 368612030042367702⟩, true⟩

def words09 : List Nat := [371285220492688822, 371285220524294042, 371285220567507990, 371285220570228889, 371285220399107824, 371285220183032072, 371285219965878891, 371285219910806279, 371285219786449846, 371285219730183702]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 78790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 78700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 78700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk787B
