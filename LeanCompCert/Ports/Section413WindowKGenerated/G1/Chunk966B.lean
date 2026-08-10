import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk966A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk966B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk966A

def state06 : KState := ⟨⟨362492529058835362, 362492671220230684⟩, ⟨(-721720678390061648), (-712443134259699384)⟩, true⟩

def words05 : List Nat := [371285299768395492, 371285299860696062, 371285300030395945, 371285300152055826, 371285300292574116, 371285300434487676, 371285300541018665, 371285300544411926, 371285300606317725, 371285300686776037]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 96650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 96600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362493500097730773, 362493642289355508⟩, ⟨(-815574150442698745), (-806293684179131601)⟩, true⟩

def words06 : List Nat := [371285300872464448, 371285300949718341, 371285301005328403, 371285301062071089, 371285301149663957, 371285301185308945, 371285301326645284, 371285301469371914, 371285301604246693, 371285301694097581]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 96660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 96600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499380169509949, 362499522391795739⟩, ⟨(-1383988924627307022), (-1374705494206078698)⟩, true⟩

def words07 : List Nat := [371285301889796245, 371285302087310498, 371285302380830359, 371285302532772868, 371285302666116855, 371285302800481274, 371285302976883608, 371285303108496722, 371285303257894323, 371285303408808326]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 96670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 96600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491884467071179, 362492026719946259⟩, ⟨(-659315839681552286), (-650029451729370642)⟩, true⟩

def words08 : List Nat := [371285303540604138, 371285303543995376, 371285303617936887, 371285303707063725, 371285303819494451, 371285303822888954, 371285303819799313, 371285303817288328, 371285303896195820, 371285303969620693]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 96680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 96600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489052338948694, 362489194622358358⟩, ⟨(-385460057609446366), (-376170717113766126)⟩, true⟩

def words09 : List Nat := [371285304070013763, 371285304171715764, 371285304270793587, 371285304274201843, 371285304293502234, 371285304320105217, 371285304451933793, 371285304496006313, 371285304538769826, 371285304582781583]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 96690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 96600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 96600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk966B
