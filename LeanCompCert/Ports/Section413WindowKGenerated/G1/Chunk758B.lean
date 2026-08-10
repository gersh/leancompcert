import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk758A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk758B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk758A

def state06 : KState := ⟨⟨362498549047157489, 362498634987624988⟩, ⟨(-1022783780032915639), (-1018381178151534441)⟩, true⟩

def words05 : List Nat := [371285209732771939, 371285209744434286, 371285209928415341, 371285209976383163, 371285210007528961, 371285210039531749, 371285210216826264, 371285210324293514, 371285210503062425, 371285210682934152]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495056913078570, 362495142877123972⟩, ⟨(-757899804759638726), (-753495414138265402)⟩, true⟩

def words06 : List Nat := [371285210861069513, 371285210863682073, 371285210956721839, 371285211083910135, 371285211262544768, 371285211297567418, 371285211299537694, 371285211300718896, 371285211472846096, 371285211606755343]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486184093114834, 362486270080731257⟩, ⟨(-84646868210893682), (-80240689133971222)⟩, true⟩

def words07 : List Nat := [371285211849672728, 371285212093679323, 371285212302280023, 371285212304893153, 371285212352858612, 371285212403982302, 371285212576258851, 371285212593584931, 371285212609492424, 371285212626439222]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487887569768113, 362487973580766103⟩, ⟨(-213855044784352797), (-209447091395783439)⟩, true⟩

def words08 : List Nat := [371285212755886536, 371285212799675234, 371285213015941600, 371285213233242857, 371285213422334822, 371285213432427815, 371285213491499582, 371285213551968958, 371285213700720193, 371285213739791603]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490976191513038, 362491062226290656⟩, ⟨(-448254179697820279), (-443844421557186667)⟩, true⟩

def words09 : List Nat := [371285213762397099, 371285213785860430, 371285213936700611, 371285214041760359, 371285214183403655, 371285214326068027, 371285214464381611, 371285214466995326, 371285214470462564, 371285214550745444]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk758B
