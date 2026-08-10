import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk586A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk586B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk586A

def state06 : KState := ⟨⟨362485736933521271, 362485787295367583⟩, ⟨(-46416245555417905), (-44420675578549025)⟩, true⟩

def words05 : List Nat := [371285028662294938, 371285029101708775, 371285029481959815, 371285029483941308, 371285029554876310, 371285029635682949, 371285030006320513, 371285030022073254, 371285030036464050, 371285030051618269]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478475241529028, 362478525621084376⟩, ⟨379680980003671886, 381677588886914146⟩, true⟩

def words06 : List Nat := [371285030356741279, 371285030517702770, 371285030825976587, 371285031135054216, 371285031398744240, 371285031400726063, 371285031276836515, 371285031160845760, 371285031117394751, 371285031119446178]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484304514746159, 362484354912394663⟩, ⟨37660926092360410, 39658596590918132⟩, true⟩

def words07 : List Nat := [371285031010062969, 371285030873303995, 371285030803961229, 371285030806198154, 371285030890950303, 371285030978968670, 371285031065490730, 371285031067473088, 371285030766621030, 371285030757599008]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473966656599529, 362474017071928934⟩, ⟨644348390243894366, 646347098348575898⟩, true⟩

def words08 : List Nat := [371285030827670776, 371285030829664142, 371285030690201704, 371285030554669107, 371285030418404040, 371285030270623601, 371285029977399830, 371285029975672780, 371285029973224354, 371285029971883758]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502587417749590, 362502637850973650⟩, ⟨(-1035560242475294909), (-1033560484044322525)⟩, true⟩

def words09 : List Nat := [371285029811223786, 371285029839208199, 371285030156746436, 371285030158729394, 371285030089433912, 371285029984421835, 371285030031796917, 371285030043467480, 371285030344775394, 371285030646938893]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk586B
