import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk814A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk814B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk814A

def state06 : KState := ⟨⟨362483235580375416, 362483335222288833⟩, ⟨146533720472415610, 152014566537963846⟩, true⟩

def words05 : List Nat := [371285200844596571, 371285201031274412, 371285201210246965, 371285201213067035, 371285201206876819, 371285201207635546, 371285201354918786, 371285201365184026, 371285201367351028, 371285201347583923]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362502385682545676, 362502485349688687⟩, ⟨(-1413512744392567997), (-1408029842995381653)⟩, true⟩

def words06 : List Nat := [371285201400332845, 371285201403440611, 371285201552848423, 371285201705017734, 371285201831572407, 371285201890480438, 371285202061965809, 371285202234912338, 371285202545210256, 371285202760264286]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495482715321593, 362495582408224532⟩, ⟨(-851079262620392443), (-845594262435915237)⟩, true⟩

def words07 : List Nat := [371285202972533326, 371285203185787344, 371285203450059731, 371285203645178656, 371285203883425856, 371285204122719833, 371285204330843999, 371285204338903866, 371285204468186756, 371285204599134856]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482803624792170, 362482903342816931⟩, ⟨182087284048854525, 187574331289342675⟩, true⟩

def words08 : List Nat := [371285204823210877, 371285204863373705, 371285204896323819, 371285204930214800, 371285204996808834, 371285204999949879, 371285205046261129, 371285205103116919, 371285205147861684, 371285205150784650]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499448238199466, 362499547981678483⟩, ⟨(-1174343576201718194), (-1168854454563503256)⟩, true⟩

def words09 : List Nat := [371285205207496187, 371285205293879880, 371285205510689217, 371285205603496220, 371285205672513571, 371285205742413159, 371285205910941798, 371285206028179998, 371285206206082860, 371285206385200360]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk814B
