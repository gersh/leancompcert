import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk418

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362454462181303718, 362454487063317118⟩, ⟨1280081564517705668, 1280784337342577786⟩, true⟩

def state01 : KState := ⟨⟨362477040123850184, 362477065018165249⟩, ⟨336258186242725974, 336961473340110294⟩, true⟩

def words00 : List Nat := [371285127104855783, 371285126945509167, 371285126499396467, 371285126417130803, 371285126334438150, 371285126154092143, 371285125211298562, 371285124740333794, 371285124367932896, 371285124369357311]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 41800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 41800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488004387384106, 362488029294228257⟩, ⟨(-122212972726897080), (-121509161725484206)⟩, true⟩

def words01 : List Nat := [371285124177653933, 371285123803741477, 371285123625700786, 371285123627232373, 371285123710480805, 371285123838943408, 371285123950150089, 371285123951550944, 371285123764995379, 371285123836163518]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 41810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 41800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480422596967576, 362480447516056716⟩, ⟨194919680340762397, 195624003492173175⟩, true⟩

def words02 : List Nat := [371285124280211848, 371285124281597194, 371285124213728124, 371285124144240227, 371285124074228071, 371285124013599506, 371285123824379120, 371285123983741024, 371285124158272312, 371285124159697457]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 41820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 41800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492170529972104, 362492195461541583⟩, ⟨(-296493727220290598), (-295788881954738848)⟩, true⟩

def words03 : List Nat := [371285124400965263, 371285124754782895, 371285125401442284, 371285125505221318, 371285125522471619, 371285125540136924, 371285125761819760, 371285125766109056, 371285125936029814, 371285126106555930]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 41830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 41800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487935553669681, 362487960497666827⟩, ⟨(-119372225098484820), (-118666859796157868)⟩, true⟩

def words04 : List Nat := [371285126275825518, 371285126277202390, 371285125685646257, 371285125665779963, 371285125795321509, 371285125796722963, 371285125511534612, 371285125140694852, 371285124967767275, 371285125037109227]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 41840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 41800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362469106018013039, 362469130974420074⟩, ⟨668859789808501673, 669565674526594369⟩, true⟩

def words05 : List Nat := [371285125676542638, 371285126316492559, 371285126840436067, 371285126841817020, 371285126781824520, 371285126747993171, 371285127091952733, 371285127093330087, 371285126712703613, 371285126332148851]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 41850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 41800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362493343105790909, 362493368074506050⟩, ⟨(-345762067036273797), (-345055667036219089)⟩, true⟩

def words06 : List Nat := [371285125999235948, 371285126000753351, 371285126098196961, 371285126433171824, 371285126682165145, 371285126683552183, 371285126450362456, 371285126453047950, 371285126953733015, 371285127151981243]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 41860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 41800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490010707804420, 362490035689085517⟩, ⟨(-206198384546504502), (-205491458345991828)⟩, true⟩

def words07 : List Nat := [371285127272719674, 371285127393932268, 371285127887601646, 371285128178430105, 371285128609068277, 371285129040203665, 371285129347868927, 371285129349247050, 371285129014531984, 371285129133407621]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 41870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 41800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478149183360139, 362478174176944458⟩, ⟨290594755751002993, 291302197272043549⟩, true⟩

def words08 : List Nat := [371285129454738196, 371285129456116958, 371285129119328323, 371285128734004207, 371285128348183051, 371285128134175177, 371285127859194879, 371285128007696345, 371285128154922177, 371285128156349377]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 41880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 41800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505994715526431, 362506019721538085⟩, ⟨(-875937274649497062), (-875229312482748816)⟩, true⟩

def words09 : List Nat := [371285128318348921, 371285128647032671, 371285129544606689, 371285129683709049, 371285129722221082, 371285129761141177, 371285130368991521, 371285130692765476, 371285131192256769, 371285131692314851]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 41890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 41800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 41800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk418
