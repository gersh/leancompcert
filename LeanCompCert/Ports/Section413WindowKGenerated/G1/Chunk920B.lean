import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk920A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk920B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk920A

def state06 : KState := ⟨⟨362491077523162371, 362491205990292133⟩, ⟨(-570012305598084690), (-562027227996732920)⟩, true⟩

def words05 : List Nat := [371285100445545790, 371285100582175845, 371285100774902932, 371285100811408356, 371285100823818380, 371285100837248916, 371285100898513957, 371285100908112745, 371285100976626168, 371285101046526622]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 92050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 92000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485992994671472, 362486121490885218⟩, ⟨(-101944974226465343), (-93957219012643151)⟩, true⟩

def words06 : List Nat := [371285101114764834, 371285101117983316, 371285101056715862, 371285101077867190, 371285101133479484, 371285101136713445, 371285101079282394, 371285101022705675, 371285100989492956, 371285101004314934]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 92060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 92000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482298409829951, 362482426935067965⟩, ⟨238243429359349536, 246233856988574794⟩, true⟩

def words07 : List Nat := [371285101066301061, 371285101129595898, 371285101188310806, 371285101191536510, 371285101128083682, 371285101085071153, 371285101111482515, 371285101114757558, 371285101090086646, 371285101064705113]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 92070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 92000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487624013552875, 362487752567561071⟩, ⟨(-252137953395390223), (-244144876456790409)⟩, true⟩

def words08 : List Nat := [371285101068881591, 371285101072429426, 371285101143267092, 371285101239993641, 371285101306606806, 371285101309827362, 371285101268989504, 371285101302764522, 371285101409092409, 371285101441213689]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 92080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 92000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478664900347460, 362478793483701659⟩, ⟨572987438194671071, 580983217752239749⟩, true⟩

def words09 : List Nat := [371285101472215563, 371285101504381994, 371285101595341616, 371285101628835691, 371285101692333595, 371285101757110141, 371285101818842179, 371285101822061875, 371285101726497494, 371285101661961727]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 92090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 92000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 92000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk920B
