import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk721A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk721B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk721A

def state06 : KState := ⟨⟨362473651654523968, 362473729114598791⟩, ⟨828415525099445429, 832190352784934521⟩, true⟩

def words05 : List Nat := [371285261923605720, 371285262028712591, 371285262132377976, 371285262134854899, 371285262013583963, 371285261951750136, 371285261980656613, 371285261983132932, 371285261842990228, 371285261686006565]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 72150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 72100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485152552688814, 362485230034939204⟩, ⟨(-1538570136265081), 2237857852247365⟩, true⟩

def words06 : List Nat := [371285261559887354, 371285261562647504, 371285261524408773, 371285261524450388, 371285261523748725, 371285261479000018, 371285261177656751, 371285261069428022, 371285261040476407, 371285261043084587]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 72160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 72100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487307761623645, 362487385266419711⟩, ⟨(-157073180211871320), (-153295124986839802)⟩, true⟩

def words07 : List Nat := [371285261044538298, 371285261010066283, 371285261129248911, 371285261205799559, 371285261341177605, 371285261477544084, 371285261578448536, 371285261580925410, 371285261473866927, 371285261506358382]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 72170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 72100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484912005732965, 362484989532583151⟩, ⟨15892452271994529, 19672099478767195⟩, true⟩

def words08 : List Nat := [371285261632568925, 371285261635069500, 371285261635392042, 371285261637109177, 371285261694932561, 371285261697662891, 371285261791253668, 371285261914285279, 371285262034513620, 371285262037077940]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 72180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 72100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486013810294211, 362486091359600866⟩, ⟨(-63660588970437713), (-59879320521744221)⟩, true⟩

def words09 : List Nat := [371285262111745266, 371285262191477913, 371285262368900323, 371285262371377706, 371285262293424789, 371285262185162476, 371285262075920940, 371285262068355399, 371285262003315845, 371285262017617767]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 72190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 72100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 72100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk721B
