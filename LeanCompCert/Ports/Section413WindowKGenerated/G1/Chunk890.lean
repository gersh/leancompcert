import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk890

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493219091541699, 362493338847441249⟩, ⟨(-735516331741944086), (-728319963816205778)⟩, true⟩

def state01 : KState := ⟨⟨362482648373932667, 362482768157809895⟩, ⟨205278037946307063, 212476896029208889⟩, true⟩

def words00 : List Nat := [371285155639085809, 371285155642188486, 371285155569463736, 371285155598774579, 371285155632549531, 371285155635652448, 371285155512354299, 371285155390068229, 371285155266869296, 371285155270449253]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 89000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 89000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362470593077389011, 362470712889208850⟩, ⟨1278408832459060875, 1285610177857416011⟩, true⟩

def words01 : List Nat := [371285155272646562, 371285155302976410, 371285155332122706, 371285155335225682, 371285155196101095, 371285155086484058, 371285154987936573, 371285154991040657, 371285154860811382, 371285154702035827]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 89010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 89000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483166912199948, 362483286751801272⟩, ⟨159049253427048473, 166253072075254091⟩, true⟩

def words02 : List Nat := [371285154541910728, 371285154509158533, 371285154417102064, 371285154391028400, 371285154363930525, 371285154317965035, 371285154166007134, 371285154129522864, 371285154131176333, 371285154134392256]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 89020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 89000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480709860158549, 362480829728115657⟩, ⟨377814322486409438, 385020665786453432⟩, true⟩

def words03 : List Nat := [371285154115737943, 371285154089115854, 371285154061838420, 371285154065290230, 371285154043158622, 371285154053612293, 371285154061494327, 371285154064598308, 371285153904188575, 371285153859582262]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 89030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 89000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472568842485383, 362472688738064681⟩, ⟨1102748779209689998, 1109957582132656198⟩, true⟩

def words04 : List Nat := [371285153890546087, 371285153893650156, 371285153811713695, 371285153722709647, 371285153632560947, 371285153550233942, 371285153415034435, 371285153333485235, 371285153250861549, 371285153169082454]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 89040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 89000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490198679018977, 362490318602616851⟩, ⟨(-467258216617327751), (-460046918499556881)⟩, true⟩

def words05 : List Nat := [371285153031217821, 371285153020893610, 371285153067712127, 371285153070870698, 371285153027111985, 371285152963036140, 371285152956060316, 371285152959481738, 371285153015073030, 371285153076533610]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470967854326625, 362471087805961262⟩, ⟨1245475929707008560, 1252689724925245340⟩, true⟩

def words06 : List Nat := [371285153112660395, 371285153115765099, 371285152983691929, 371285152898286667, 371285152811284861, 371285152754646310, 371285152529293258, 371285152281184052, 371285152031786064, 371285151909755191]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467245338569121, 362467365318181714⟩, ⟨1577098769821600750, 1584315057178628854⟩, true⟩

def words07 : List Nat := [371285151753962961, 371285151725407113, 371285151695778806, 371285151665112430, 371285151465639987, 371285151274249059, 371285151081267639, 371285151007629960, 371285150820297457, 371285150624167105]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472254130064942, 362472374137511466⟩, ⟨1130963285256590535, 1138182052198498933⟩, true⟩

def words08 : List Nat := [371285150426619538, 371285150343362494, 371285150211578755, 371285150206919874, 371285150201322008, 371285150176517950, 371285149982836937, 371285149916698295, 371285149848962147, 371285149780705972]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470886066474190, 362471006102209639⟩, ⟨1252862566560289857, 1260083853896313925⟩, true⟩

def words09 : List Nat := [371285149639654259, 371285149494447407, 371285149348008806, 371285149285168975, 371285149166800509, 371285149078244319, 371285148988557016, 371285148884852510, 371285148612314615, 371285148457472224]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk890
