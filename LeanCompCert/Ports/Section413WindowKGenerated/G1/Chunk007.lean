import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk007

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨361886568871321764, 361886568875936484⟩, ⟨393946441437792200, 393946443640996452⟩, true⟩

def state01 : KState := ⟨⟨362495598188073715, 362495598192829127⟩, ⟨(-30343414719211858), (-30343412416796622)⟩, true⟩

def words00 : List Nat := [371249746279217498, 371250173345418657, 371251729630074392, 371253281499744574, 371254498204679768, 371254498204695455, 371253102065163749, 371252369457488013, 371252860992225770, 371252921100822381]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362404610587248187, 362404610592149929⟩, ⟨36003257309732068, 36003259716793228⟩, true⟩

def words01 : List Nat := [371252987397778162, 371253053508772880, 371254286980204192, 371254904258053643, 371255503614804185, 371256101299714540, 371256653790189130, 371256653790205257, 371254684666840255, 371254615119534365]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361780259314280283, 361780259319326937⟩, ⟨487981189899037959, 487981192411197597⟩, true⟩

def words02 : List Nat := [371255161222059471, 371255161222075670, 371253778911948952, 371252375505769841, 371250975971050307, 371249947855441022, 371248410861141059, 371248569000289669, 371248726706174803, 371248726706191592]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362979278822135339, 362979278827330162⟩, ⟨(-394197175340398096), (-394197172719305260)⟩, true⟩

def words03 : List Nat := [371247851195294580, 371247890034212674, 371249751316723982, 371249751316740377, 371249194362716334, 371248181414970945, 371247171216059585, 371246931454511726, 371246579945258840, 371247298837155661]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362000026608552402, 362000026613897778⟩, ⟨336282969815474022, 336282972548751342⟩, true⟩

def words04 : List Nat := [371247972983497884, 371247972983514718, 371248368593143832, 371249455390833561, 371250983392049993, 371250983392066655, 371250168002020731, 371249356962467348, 371248548088567303, 371248403910629447]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361867605610788445, 361867605616286000⟩, ⟨444226877763424925, 444226880611613287⟩, true⟩

def words05 : List Nat := [371248949229045708, 371250088553657232, 371251195529228332, 371251195529245234, 371251136392596077, 371251335733842247, 371253245060746763, 371253245060763674, 371252884773857962, 371252114669722334]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362627815626261233, 362627815631912363⟩, ⟨(-136071635752040002), (-136071632786339726)⟩, true⟩

def words06 : List Nat := [371252277626576295, 371252397485314512, 371253176952050033, 371253954380970422, 371254285176643728, 371254285176660837, 371252395127792565, 371251407982144878, 371251099225678191, 371251328429854854]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362309640507268903, 362309640513078258⟩, ⟨115299198768143437, 115299201856496135⟩, true⟩

def words07 : List Nat := [371251532169446411, 371251735381903525, 371253577978527464, 371254653006123757, 371256163569667575, 371257670245023495, 371258738827003396, 371258738827020817, 371257649758058847, 371257460002637869]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361932673361734946, 361932673367702000⟩, ⟨411981166352442156, 411981169564622456⟩, true⟩

def words08 : List Nat := [371257798639090232, 371257798639107899, 371256960276790250, 371256009324367754, 371255060794746953, 371254553593375013, 371253581637059824, 371253886373126774, 371254168519031236, 371254168519049624]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362855582043153598, 362855582049283761⟩, ⟨(-323947130716803430), (-323947127374944906)⟩, true⟩

def words09 : List Nat := [371253509233156464, 371253494256544701, 371254359304124604, 371254359304142516, 371253179210597181, 371251757868216902, 371250462159351869, 371250462159372015, 371250648140044630, 371251153675532270]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk007
