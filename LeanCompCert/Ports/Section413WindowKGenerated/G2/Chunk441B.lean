import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk441A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk441B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk441A

def state06 : KState := ⟨⟨360589474479676254, 360589486589294848⟩, ⟨(-274892345661651249), (-274530962687857589)⟩, true⟩

def words05 : List Nat := [360583268591329459, 360583268411332556, 360583268412488916, 360583269010234583, 360583269477062105, 360583269943978690, 360583270084522736, 360583270085126172, 360583269854849470, 360583269996312628]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571563955352854, 360571576070661186⟩, ⟨515966426365112074, 516328060626236212⟩, true⟩

def words06 : List Nat := [360583270099211426, 360583270099815003, 360583269860606106, 360583269226657609, 360583268592642755, 360583267599980379, 360583266968083683, 360583266609634216, 360583266251135090, 360583265635085598]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360623237906109687, 360623250027113395⟩, ⟨(-1766744305882020430), (-1766382420028486426)⟩, true⟩

def words07 : List Nat := [360583265618333759, 360583265866397776, 360583266502229066, 360583266988563366, 360583267074226907, 360583267159935532, 360583267232827454, 360583267626669698, 360583268532146423, 360583269437719120]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579978462680040, 360579990589436552⟩, ⟨144429577059083714, 144791717100122822⟩, true⟩

def words08 : List Nat := [360583270084305068, 360583270219875074, 360583270284831128, 360583270349970638, 360583270350475876, 360583270285008076, 360583269708482008, 360583268688896125, 360583267669240783, 360583267161446060]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569165427526954, 360569177559979834⟩, ⟨622215682126216659, 622578073917619275⟩, true⟩

def words09 : List Nat := [360583267087797184, 360583266870639676, 360583266653426066, 360583266178945242, 360583265487721157, 360583264666322971, 360583263844784432, 360583263419971426, 360583263354818028, 360583263036765301]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk441B
