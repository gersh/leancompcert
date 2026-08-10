import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk578A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk578B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk578A

def state06 : KState := ⟨⟨360616737331928500, 360616758583864637⟩, ⟨(-2015533433086638050), (-2014702681783175106)⟩, true⟩

def words05 : List Nat := [360581936375463653, 360581936588560052, 360581937100286156, 360581937314016108, 360581937314775896, 360581937267871347, 360581937374529642, 360581937678417576, 360581938280883705, 360581938883517544]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 57850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 57800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594095893579289, 360594117153219577⟩, ⟨(-705446123292988507), (-704614926189345383)⟩, true⟩

def words06 : List Nat := [360581939335653139, 360581939795347619, 360581940342597355, 360581940890061914, 360581941308824178, 360581941429707071, 360581941430426726, 360581941400533474, 360581941370494428, 360581941539765700]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 57860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 57800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360563435305009723, 360563456572256442⟩, ⟨1069071326731933813, 1069902964056993599⟩, true⟩

def words07 : List Nat := [360581941795094874, 360581942050565486, 360581942130119117, 360581942130928699, 360581942082698598, 360581941954523719, 360581941875111198, 360581941875919403, 360581941738131094, 360581941419596750]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 57870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 57800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588050872775784, 360588072147660919⟩, ⟨(-355765416737261625), (-354933337263034397)⟩, true⟩

def words08 : List Nat := [360581941100890492, 360581941287893242, 360581941486867238, 360581941685978409, 360581941686725498, 360581941584638770, 360581941262709765, 360581941171633333, 360581941080317278, 360581941085194162]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 57880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 57800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360563463496667997, 360563484779241310⟩, ⟨1067685895197501007, 1068518419779099297⟩, true⟩

def words09 : List Nat := [360581941085915207, 360581941002916011, 360581940919770478, 360581940761822045, 360581940752691589, 360581940667305158, 360581940581852829, 360581940263128979, 360581939646619887, 360581939328805716]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 57890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 57800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 57800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk578B
