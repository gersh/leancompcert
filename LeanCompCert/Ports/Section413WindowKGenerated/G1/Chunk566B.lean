import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk566A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk566B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk566A

def state06 : KState := ⟨⟨362498441086158840, 362498487942903963⟩, ⟨(-771393505280930463), (-769600061542025595)⟩, true⟩

def words05 : List Nat := [371284905983935681, 371284905791776057, 371284905691923654, 371284905693841273, 371284905490652887, 371284905236764347, 371284904993808636, 371284904995953212, 371284905165248041, 371284905407093758]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481332343902016, 362481379217853407⟩, ⟨198004417951809015, 199798836687168459⟩, true⟩

def words06 : List Nat := [371284905536743136, 371284905538653032, 371284905388374050, 371284905470621194, 371284905569666125, 371284905571577005, 371284905334796774, 371284905093981151, 371284904870108362, 371284904872285862]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474179039194620, 362474225930390827⟩, ⟨603510486759985453, 605305882844706715⟩, true⟩

def words07 : List Nat := [371284905060510399, 371284905311795656, 371284905561030885, 371284905562941163, 371284905449801871, 371284905430015548, 371284905597639502, 371284905599554349, 371284905472367931, 371284905286122033]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362499308729459659, 362499355637736929⟩, ⟨(-820928236625004157), (-819131872296955473)⟩, true⟩

def words08 : List Nat := [371284905221875790, 371284905226414333, 371284905389656135, 371284905553643638, 371284905668565864, 371284905670508987, 371284905693985252, 371284905862994148, 371284906317144796, 371284906574000235]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482462422840736, 362482509348548593⟩, ⟨134194955369983280, 135992307922394522⟩, true⟩

def words09 : List Nat := [371284906831031460, 371284907088667313, 371284907406463983, 371284907614818336, 371284907774954034, 371284907935829752, 371284908095206056, 371284908097116393, 371284907841840769, 371284907801951105]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk566B
