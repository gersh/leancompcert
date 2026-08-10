import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk890A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk890B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk890A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk890B
