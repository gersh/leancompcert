import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk920

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496905271364920, 362497033564636670⟩, ⟨(-1106023213863705509), (-1098054136424235371)⟩, true⟩

def state01 : KState := ⟨⟨362490593362560982, 362490721684877005⟩, ⟨(-525340572967944832), (-517368823310328414)⟩, true⟩

def words00 : List Nat := [371285098435758830, 371285098438975188, 371285098488679702, 371285098575332124, 371285098696610389, 371285098699827021, 371285098675006821, 371285098651722058, 371285098718232230, 371285098783014072]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 92000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 92000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478728208414975, 362478856559655789⟩, ⟨566489669412522370, 574464080584973836⟩, true⟩

def words01 : List Nat := [371285098947355743, 371285099112974348, 371285099277315287, 371285099329168471, 371285099363411842, 371285099399275748, 371285099492532471, 371285099495749635, 371285099441567363, 371285099377310484]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 92010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 92000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484776996982573, 362484905377039261⟩, ⟨9888445107017757, 17865508065359185⟩, true⟩

def words02 : List Nat := [371285099318190524, 371285099321799096, 371285099337186436, 371285099389670815, 371285099422035932, 371285099425276496, 371285099397167302, 371285099425158061, 371285099500711001, 371285099504042036]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 92020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 92000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488970709703582, 362489099119122059⟩, ⟨(-376065812127165678), (-368086046859028042)⟩, true⟩

def words03 : List Nat := [371285099504337355, 371285099505554176, 371285099621088871, 371285099681165503, 371285099769444981, 371285099858994326, 371285099925917902, 371285099929144515, 371285099918574693, 371285099966061369]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 92030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 92000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486336396954957, 362486464835063470⟩, ⟨(-133588248983115851), (-125605842936910893)⟩, true⟩

def words04 : List Nat := [371285100129673003, 371285100137037717, 371285100139510084, 371285100125641119, 371285100112302431, 371285100115857197, 371285100150880141, 371285100225354515, 371285100292365683, 371285100310583162]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 92040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 92000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk920
