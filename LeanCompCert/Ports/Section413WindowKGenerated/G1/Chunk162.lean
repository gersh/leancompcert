import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk162

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362537290020753115, 362537293469604825⟩, ⟨(-849200240546318098), (-849162446813391812)⟩, true⟩

def state01 : KState := ⟨⟨362464626185733170, 362464629638975970⟩, ⟨328331210743413196, 328369075635329206⟩, true⟩

def words00 : List Nat := [371284884845068956, 371284885344940233, 371284885345311857, 371284885161404580, 371284885024399304, 371284885024943195, 371284884554329862, 371284885684408972, 371284886830052482, 371284886830563591]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 16200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 16200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362535595728153589, 362535599185863023⟩, ⟨(-822442002441171761), (-822404065122406739)⟩, true⟩

def words01 : List Nat := [371284885813842751, 371284886046945734, 371284889398886505, 371284889649540734, 371284889649923736, 371284888933243349, 371284891306706423, 371284892972188827, 371284896098684121, 371284899225002262]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 16210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 16200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362518508703591917, 362518512165760064⟩, ⟨(-545457663433934214), (-545419653772051490)⟩, true⟩

def words02 : List Nat := [371284902325814119, 371284902326308477, 371284902207069345, 371284904049922038, 371284905653908791, 371284905654412811, 371284904981569729, 371284904226636376, 371284906518014280, 371284908589038233]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 16220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 16200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466703050031681, 362466706516666423⟩, ⟨295864805933242597, 295902888110258971⟩, true⟩

def words03 : List Nat := [371284914460609100, 371284920331661157, 371284925468959384, 371284925549969656, 371284925993791286, 371284926437804651, 371284929356113419, 371284929356608994, 371284928259312274, 371284927137855479]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 16230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 16200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487178722207376, 362487182193266621⟩, ⟨(-36589033430333438), (-36550879376437988)⟩, true⟩

def words04 : List Nat := [371284928093985982, 371284928295376753, 371284931403364105, 371284934511165099, 371284937228964745, 371284937229459866, 371284934899460244, 371284932971531048, 371284932907866577, 371284933046790932]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 16240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 16200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362540492579926642, 362540496055491005⟩, ⟨(-903141405417767597), (-903103178132903631)⟩, true⟩

def words05 : List Nat := [371284933161846826, 371284933277052173, 371284937182632788, 371284939783627706, 371284943491766347, 371284947199644629, 371284950884542239, 371284951237638212, 371284954654015189, 371284958070242072]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 16250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 16200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472860936743641, 362472864416725543⟩, ⟨196921147074347449, 196959446211475845⟩, true⟩

def words06 : List Nat := [371284962218276920, 371284962218772665, 371284962213210699, 371284962191162943, 371284963254837541, 371284963255383134, 371284965464432329, 371284968461088059, 371284970098216896, 371284970098729937]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 16260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 16200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362568817684012312, 362568821168480267⟩, ⟨(-1364721285706908393), (-1364682913559440885)⟩, true⟩

def words07 : List Nat := [371284971719186694, 371284974083623682, 371284980228843735, 371284982013560381, 371284983178153295, 371284984342747893, 371284988250521591, 371284990286470095, 371284995436124188, 371285000585373613]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 16270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 16200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362508978862977233, 362508982351928972⟩, ⟨(-390237333315630097), (-390198888149395589)⟩, true⟩

def words08 : List Nat := [371285005462451392, 371285007236861757, 371285011728731794, 371285016220300717, 371285021816508137, 371285023620987609, 371285025149420031, 371285026677838632, 371285029074001130, 371285030544909797]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 16280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 16200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362460587299735056, 362460590793147819⟩, ⟨398437127573068609, 398475645432459029⟩, true⟩

def words09 : List Nat := [371285033895976278, 371285037246825873, 371285040574629792, 371285040575126412, 371285038886000052, 371285038303787188, 371285040162785980, 371285040163283125, 371285038651078576, 371285037151763308]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 16290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 16200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 16200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk162
