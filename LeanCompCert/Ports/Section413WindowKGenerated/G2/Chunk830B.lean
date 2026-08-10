import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk830A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk830B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk830A

def state06 : KState := ⟨⟨360599134909105196, 360599179976318199⟩, ⟨(-1394321941370480665), (-1391793927448262191)⟩, true⟩

def words05 : List Nat := [360582423005419610, 360582423132024927, 360582423310417303, 360582423377164601, 360582423378282678, 360582423313435859, 360582423248365989, 360582423283968892, 360582423486673809, 360582423689643969]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598954531907732, 360598999610492676⟩, ⟨(-1379367991227671286), (-1376839032697298738)⟩, true⟩

def words06 : List Nat := [360582423781699367, 360582423940627154, 360582424244174156, 360582424548063692, 360582424783174343, 360582424934391623, 360582425012703623, 360582425091146175, 360582425165480029, 360582425366379842]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360584806571406138, 360584851661207063⟩, ⟨(-203954226855313192), (-201424336558304118)⟩, true⟩

def words07 : List Nat := [360582425711707500, 360582426057263402, 360582426329922190, 360582426498896245, 360582426629597546, 360582426760635752, 360582427036123678, 360582427167310308, 360582427197568293, 360582427227984566]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595739827708870, 360595784928769703⟩, ⟨(-1112390416087375311), (-1109859590261434063)⟩, true⟩

def words08 : List Nat := [360582427374637440, 360582427613173494, 360582427737423074, 360582427861869719, 360582427862969667, 360582427860739671, 360582427713776368, 360582427631172652, 360582427609061698, 360582427771071981]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592247520535214, 360592292632941160⟩, ⟨(-822156981438836919), (-819625212890799899)⟩, true⟩

def words09 : List Nat := [360582427860186575, 360582427949428946, 360582428183206022, 360582428527994470, 360582428836014782, 360582429144231411, 360582429340626292, 360582429392635412, 360582429512291370, 360582429632340797]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk830B
