import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk987A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk987B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk987A

def state06 : KState := ⟨⟨362483660341324121, 362483808991548748⟩, ⟨142359640020065705, 152271234710589093⟩, true⟩

def words05 : List Nat := [371285351126918195, 371285351082502408, 371285351036632422, 371285351035349355, 371285350986523311, 371285350969950912, 371285350952196993, 371285350935405829, 371285350833882063, 371285350822600901]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481935871142365, 362482084552327127⟩, ⟨312679038167593818, 322593690638333946⟩, true⟩

def words06 : List Nat := [371285350849012414, 371285350852494428, 371285350815361163, 371285350759361412, 371285350702064197, 371285350677093023, 371285350630610366, 371285350657568016, 371285350660179916, 371285350662387250]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500134025569834, 362500282738040236⟩, ⟨(-1484832935064236250), (-1474915192349046628)⟩, true⟩

def words07 : List Nat := [371285350683390787, 371285350739222994, 371285350895820264, 371285350978941387, 371285351046213073, 371285351114567249, 371285351214216005, 371285351266682212, 371285351420193666, 371285351575242238]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488896678875232, 362489045422661144⟩, ⟨(-374786681152039521), (-364865844939925283)⟩, true⟩

def words08 : List Nat := [371285351726484739, 371285351742003820, 371285351848734266, 371285351957429345, 371285352076757738, 371285352080228205, 371285352063147353, 371285352036611831, 371285352070738913, 371285352112086903]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481449355093136, 362481598130195343⟩, ⟨360969965389606640, 370893895494151388⟩, true⟩

def words09 : List Nat := [371285352163567499, 371285352216435305, 371285352268054648, 371285352271526757, 371285352205036905, 371285352171097660, 371285352182717292, 371285352186249085, 371285352151008498, 371285352116991843]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk987B
