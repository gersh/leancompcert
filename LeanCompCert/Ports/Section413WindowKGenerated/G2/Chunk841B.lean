import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk841A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk841B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk841A

def state06 : KState := ⟨⟨360560337962424185, 360560384278467878⟩, ⟨1853348683105571030, 1855981113252842170⟩, true⟩

def words05 : List Nat := [360582438674313126, 360582438594571640, 360582438514700059, 360582438364273056, 360582438217355935, 360582438035217257, 360582437852729646, 360582437736968938, 360582437546781640, 360582437285992271]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 84150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 84100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360570811788766645, 360570858116232350⟩, ⟨971780870059494168, 974414261538088614⟩, true⟩

def words06 : List Nat := [360582437024958914, 360582436691828136, 360582436449965346, 360582436349381249, 360582436248706227, 360582436033425121, 360582435676941689, 360582435368493718, 360582435059662623, 360582434856894559]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 84160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 84100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560223251909046, 360560269590871436⟩, ⟨1863067528857083282, 1865701888068077548⟩, true⟩

def words07 : List Nat := [360582434720432493, 360582434513456710, 360582434306246582, 360582434182681610, 360582434129608729, 360582433946011555, 360582433762297398, 360582433500171475, 360582433096874844, 360582432834968230]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 84170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 84100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565156815172839, 360565203165533506⟩, ⟨1447769638044801052, 1450404956819774976⟩, true⟩

def words08 : List Nat := [360582432572664036, 360582432451592286, 360582432336798441, 360582432114937469, 360582431892881489, 360582431618621870, 360582431415148912, 360582431289287903, 360582431163313523, 360582430923661785]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 84180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 84100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360604871710829423, 360604918072586582⟩, ⟨(-1896046028999189222), (-1893409750696838240)⟩, true⟩

def words09 : List Nat := [360582430720011566, 360582430657663870, 360582430624738708, 360582430685872530, 360582430686997505, 360582430627970727, 360582430624123567, 360582430751615868, 360582431019663079, 360582431287979549]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 84190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 84100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 84100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk841B
