import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk568A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk568B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk568A

def state06 : KState := ⟨⟨362484698849034042, 362484746050373908⟩, ⟨8781008189857771, 10594011174158655⟩, true⟩

def words05 : List Nat := [371284930857147410, 371284931149141981, 371284931441791531, 371284931526748177, 371284931684928196, 371284931844069509, 371284932311617542, 371284932367541527, 371284932368983878, 371284932367840918]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482301887147964, 362482349105679226⟩, ⟨145122025079934256, 146936005653130836⟩, true⟩

def words06 : List Nat := [371284932490125538, 371284932499112874, 371284932764723839, 371284933031131282, 371284933198080871, 371284933199997217, 371284932954662638, 371284932863153743, 371284932821030714, 371284932823028499]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362479503895551795, 362479551131553564⟩, ⟨304299208982955318, 306114183191072690⟩, true⟩

def words07 : List Nat := [371284932779044021, 371284932718054166, 371284932902436628, 371284932996682793, 371284933094845613, 371284933193689911, 371284933290933809, 371284933292850530, 371284932978024053, 371284932885829076]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473921490467688, 362473968743561337⟩, ⟨621901238731267462, 623717185214388566⟩, true⟩

def words08 : List Nat := [371284932856137393, 371284932858092917, 371284932725172254, 371284932574676124, 371284932423470155, 371284932348045165, 371284932226623728, 371284932300832035, 371284932306091189, 371284932308075565]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505017236968598, 362505064507375741⟩, ⟨(-1147269796118294099), (-1145452864583617045)⟩, true⟩

def words09 : List Nat := [371284932232993451, 371284932351606403, 371284932778250789, 371284932793787284, 371284932795271185, 371284932763206349, 371284933005082215, 371284933168328522, 371284933523435067, 371284933879362462]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk568B
