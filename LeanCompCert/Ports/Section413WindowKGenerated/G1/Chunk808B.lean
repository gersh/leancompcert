import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk808A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk808B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk808A

def state06 : KState := ⟨⟨362481976964652162, 362482075088378651⟩, ⟨244039315724963569, 249396945001820569⟩, true⟩

def words05 : List Nat := [371285158461823145, 371285158737830531, 371285159012990503, 371285159085032720, 371285159189198803, 371285159294802226, 371285159462282425, 371285159465079773, 371285159428919499, 371285159393906747]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 80850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 80800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484734016155154, 362484832164912431⟩, ⟨21131385753500911, 26491039147336255⟩, true⟩

def words06 : List Nat := [371285159398004191, 371285159401086954, 371285159483439584, 371285159603219454, 371285159694577269, 371285159697374861, 371285159611691326, 371285159642018807, 371285159737620705, 371285159740517073]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 80860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 80800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489847764236457, 362489945938544643⟩, ⟨(-392459670476312722), (-387097950651107020)⟩, true⟩

def words07 : List Nat := [371285159738594349, 371285159707808443, 371285159743347330, 371285159746459430, 371285159778663757, 371285159820484650, 371285159861493439, 371285159864341125, 371285159857508692, 371285159920188650]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 80870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 80800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480788848376821, 362480887047584382⟩, ⟨340283189524222814, 345646923340583708⟩, true⟩

def words08 : List Nat := [371285160096474591, 371285160099274260, 371285160099049827, 371285160066079807, 371285160032097921, 371285160006124295, 371285159988450428, 371285160046597084, 371285160093560158, 371285160096457427]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 80800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494789180294443, 362494887404822044⟩, ⟨(-792250169427792992), (-786884387348734882)⟩, true⟩

def words09 : List Nat := [371285160101251922, 371285160160380511, 371285160333425957, 371285160370402205, 371285160381477802, 371285160393465560, 371285160556977258, 371285160649275255, 371285160771448559, 371285160894799316]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 80890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 80800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 80800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk808B
