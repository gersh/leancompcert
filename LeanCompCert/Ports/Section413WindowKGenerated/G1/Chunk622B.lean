import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk622A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk622B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk622A

def state06 : KState := ⟨⟨362481491807684567, 362481548809066873⟩, ⟨238347726036126884, 240744850452951452⟩, true⟩

def words05 : List Nat := [371285415316766953, 371285415487587416, 371285415658815184, 371285415660933478, 371285415568218103, 371285415554294587, 371285415692147486, 371285415694296970, 371285415634794115, 371285415575055517]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 62250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 62200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490503842577063, 362490560862843449⟩, ⟨(-322778165338785938), (-320379865101030862)⟩, true⟩

def words06 : List Nat := [371285415636461381, 371285415638813454, 371285415765773519, 371285415899350837, 371285415960495740, 371285415962608838, 371285415709931998, 371285415681128872, 371285415849161803, 371285415933982486]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 62260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 62200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478485490151470, 362478542529731177⟩, ⟨425717481078258609, 428116984050346955⟩, true⟩

def words07 : List Nat := [371285415935592917, 371285415930626962, 371285416175482768, 371285416309173351, 371285416494026367, 371285416679661158, 371285416863617467, 371285416865730960, 371285416705910865, 371285416598196983]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 62270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 62200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485139318364397, 362485196376776395⟩, ⟨11330583983290615, 13731259928100091⟩, true⟩

def words08 : List Nat := [371285416596709712, 371285416598842245, 371285416533257019, 371285416467386891, 371285416410379083, 371285416412748866, 371285416490226211, 371285416653489570, 371285416815428325, 371285416817616468]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 62280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 62200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362501387640451590, 362501444717967960⟩, ⟨(-1000893028215306327), (-998491162161972461)⟩, true⟩

def words09 : List Nat := [371285417040663477, 371285417268316981, 371285417522987385, 371285417525101582, 371285417436468369, 371285417309310049, 371285417309643731, 371285417311995222, 371285417570109036, 371285417829761319]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 62290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 62200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 62200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk622B
