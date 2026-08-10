import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk986A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk986B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk986A

def state06 : KState := ⟨⟨362491274818636245, 362491423156292001⟩, ⟨(-608884127158244245), (-599003386179275017)⟩, true⟩

def words05 : List Nat := [371285351561291617, 371285351591070548, 371285351705751276, 371285351709216834, 371285351698454634, 371285351673112309, 371285351685202948, 371285351698031755, 371285351761936316, 371285351827335481]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483820171130809, 362483968540026933⟩, ⟨126583120064720289, 136466943376428761⟩, true⟩

def words06 : List Nat := [371285351891283366, 371285351894748920, 371285351848734252, 371285351880111335, 371285351915831369, 371285351919297015, 371285351818250306, 371285351713027925, 371285351606417036, 371285351604214391]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476124108708861, 362476272508854996⟩, ⟨886048021040125359, 895934927952838967⟩, true⟩

def words07 : List Nat := [371285351670979971, 371285351753284820, 371285351836270652, 371285351839737268, 371285351796406117, 371285351786673152, 371285351848749844, 371285351852216305, 371285351791584227, 371285351703503890]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483763269923073, 362483911701099122⟩, ⟨132177601555801532, 142067570656877712⟩, true⟩

def words08 : List Nat := [371285351613864585, 371285351578332475, 371285351490083890, 371285351471245961, 371285351451395800, 371285351406197297, 371285351299132072, 371285351244238563, 371285351231106006, 371285351234695808]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480496736727024, 362480645199496509⟩, ⟨454562769519260540, 464455856731677152⟩, true⟩

def words09 : List Nat := [371285351222700666, 371285351205232664, 371285351190998704, 371285351194855667, 371285351150585166, 371285351138621908, 371285351125437372, 371285351112919651, 371285350975933649, 371285350932594095]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk986B
