import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk942A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk942B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk942A

def state06 : KState := ⟨⟨362481920604882563, 362482055532183990⟩, ⟨284733386871256126, 293320324766751054⟩, true⟩

def words05 : List Nat := [371285166864669419, 371285166894380592, 371285167035389467, 371285167131040043, 371285167230833281, 371285167331894424, 371285167430906937, 371285167434208052, 371285167382964503, 371285167354004134]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 94250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 94200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481976835736024, 362482111792464439⟩, ⟨279464456401752091, 288054168242471957⟩, true⟩

def words06 : List Nat := [371285167402812327, 371285167406171219, 371285167394642565, 371285167384037691, 371285167372144311, 371285167373173791, 371285167358478511, 371285167404089169, 371285167418261008, 371285167421702187]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 94260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 94200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496921649883860, 362497056636478848⟩, ⟨(-1129452284253234865), (-1120859756741184701)⟩, true⟩

def words07 : List Nat := [371285167453492413, 371285167519455548, 371285167696222580, 371285167724076869, 371285167732333767, 371285167741644771, 371285167830635964, 371285167877364152, 371285168005705068, 371285168135542910]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 94270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 94200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483877689090451, 362484012705516466⟩, ⟨100368172121713287, 108963512252271437⟩, true⟩

def words08 : List Nat := [371285168244054373, 371285168261684382, 371285168324971145, 371285168389936311, 371285168483901159, 371285168487203265, 371285168431384265, 371285168372054675, 371285168322769694, 371285168326603032]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 94280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 94200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470790434037642, 362470925480127054⟩, ⟨1334499338524611132, 1343097475770324406⟩, true⟩

def words09 : List Nat := [371285168416849314, 371285168520688718, 371285168623780134, 371285168627082671, 371285168580090884, 371285168568846849, 371285168571360988, 371285168574663625, 371285168442700688, 371285168295352615]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 94290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 94200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 94200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk942B
