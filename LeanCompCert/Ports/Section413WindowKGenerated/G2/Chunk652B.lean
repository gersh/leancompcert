import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk652A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk652B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk652A

def state06 : KState := ⟨⟨360568463436240707, 360568490732311326⟩, ⟨941651161429394142, 942854473596994302⟩, true⟩

def words05 : List Nat := [360582939276111367, 360582939250391533, 360582939224566103, 360582939081265775, 360582939007786134, 360582938833449478, 360582938717899485, 360582938718818965, 360582938615533627, 360582938395100125]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580466445617682, 360580493750377099⟩, ⟨158180119430930352, 159383998671022790⟩, true⟩

def words06 : List Nat := [360582938174473625, 360582937948421407, 360582937859817582, 360582937690210445, 360582937520538814, 360582937150022119, 360582936545184330, 360582936174983481, 360582935804496380, 360582935668542735]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569469727727652, 360569497041241563⟩, ⟨875998880643744282, 877203331332971734⟩, true⟩

def words07 : List Nat := [360582935631950032, 360582935477949927, 360582935323781655, 360582935362691359, 360582935363475319, 360582935324403962, 360582935285241102, 360582935128484242, 360582934797069394, 360582934592273012]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579892958223116, 360579920280411820⟩, ⟨195533992908022647, 196739009930455191⟩, true⟩

def words08 : List Nat := [360582934387174981, 360582934354797432, 360582934328748836, 360582934170368921, 360582934011847089, 360582933699496688, 360582933617548377, 360582933694210425, 360582933695044179, 360582933590412287]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588760769102308, 360588788099972084⟩, ⟨(-383462826912828221), (-382257243059462065)⟩, true⟩

def words09 : List Nat := [360582933685053136, 360582933826111440, 360582934201033657, 360582934342186851, 360582934343043041, 360582934282651651, 360582934222066613, 360582934145790297, 360582934236184751, 360582934326782402]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk652B
