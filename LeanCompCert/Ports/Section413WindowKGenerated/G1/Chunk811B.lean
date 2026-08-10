import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk811A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk811B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk811A

def state06 : KState := ⟨⟨362484562133808042, 362484661015126786⟩, ⟨36811646061725744, 42230648031380236⟩, true⟩

def words05 : List Nat := [371285181524565754, 371285181589678314, 371285181646034217, 371285181648842580, 371285181502713085, 371285181404631859, 371285181355506515, 371285181358393598, 371285181356553248, 371285181353323329]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488649885030713, 362488748791472577⟩, ⟨(-294898602875480232), (-289477561786219234)⟩, true⟩

def words06 : List Nat := [371285181486828286, 371285181555518691, 371285181774752780, 371285181995099699, 371285182177129243, 371285182179938229, 371285182244721544, 371285182333466354, 371285182476358210, 371285182523202059]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486650955893611, 362486749887959424⟩, ⟨(-132599581610776024), (-127176460501532892)⟩, true⟩

def words07 : List Nat := [371285182558608087, 371285182594982452, 371285182781902234, 371285182902405927, 371285183036310128, 371285183171305293, 371285183305352489, 371285183308163418, 371285183286023733, 371285183308827589]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482303819082211, 362482402776156162⟩, ⟨220341873029597066, 225767024429369112⟩, true⟩

def words08 : List Nat := [371285183481730113, 371285183484539626, 371285183455434076, 371285183427360648, 371285183398179408, 371285183398209693, 371285183395483530, 371285183452354666, 371285183497771126, 371285183500684175]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493909142624189, 362494008125172946⟩, ⟨(-722000649533929861), (-716573429711423317)⟩, true⟩

def words09 : List Nat := [371285183494930196, 371285183524902899, 371285183616883675, 371285183619693605, 371285183509770487, 371285183375748881, 371285183255205982, 371285183258346730, 371285183325983006, 371285183437918954]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk811B
