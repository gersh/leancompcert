import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk342

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362466077928875099, 362466094313925458⟩, ⟨637504618200098791, 637883347950335861⟩, true⟩

def state01 : KState := ⟨⟨362466240679262874, 362466257074197068⟩, ⟨631987721820093803, 632366789649207109⟩, true⟩

def words00 : List Nat := [371284745386172681, 371284745387300184, 371284744745242239, 371284744096915048, 371284743448209206, 371284743061124911, 371284742248304117, 371284742193469787, 371284742138272887, 371284741926276847]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 34200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 34200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362517104234453231, 362517120639385206⟩, ⟨(-1108273263723635883), (-1107893853819512219)⟩, true⟩

def words01 : List Nat := [371284741700708168, 371284742016000623, 371284743184949466, 371284743215991488, 371284743216849309, 371284743109577164, 371284743747409294, 371284744067249698, 371284745014133916, 371284745961444190]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 34210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 34200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467847118166475, 362467863533115202⟩, ⟨577416632663611184, 577796385390739586⟩, true⟩

def words02 : List Nat := [371284746602561762, 371284746603670703, 371284746230524230, 371284746205757380, 371284746312904098, 371284746314013055, 371284745434397423, 371284744556838755, 371284743678894358, 371284743357403568]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 34220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 34200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362448226525425333, 362448242950367359⟩, ⟨1249254347990994939, 1249634442839276145⟩, true⟩

def words03 : List Nat := [371284743225304235, 371284743586767122, 371284743945395477, 371284743946504783, 371284743168247891, 371284742494659513, 371284741820549403, 371284741387504978, 371284740348061040, 371284739283394208]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 34230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 34200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362456636786478470, 362456653221346382⟩, ⟨961336198097672689, 961716632859949229⟩, true⟩

def words04 : List Nat := [371284738218281096, 371284737845057987, 371284737150364258, 371284736889274655, 371284736627852714, 371284736231224378, 371284734698199019, 371284733767685683, 371284732836644401, 371284732539094118]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 34240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 34200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474890548024182, 362474906993006499⟩, ⟨336033953528998630, 336414734762228976⟩, true⟩

def words05 : List Nat := [371284731720128496, 371284730708841825, 371284729697173737, 371284729538174718, 371284729099201047, 371284728705345392, 371284728311126208, 371284727877135149, 371284726739296105, 371284726454032834]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 34250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 34200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362464774110895959, 362464790565753619⟩, ⟨682718270601913909, 683099390216511003⟩, true⟩

def words06 : List Nat := [371284726733440389, 371284726734551257, 371284726328107899, 371284725889626930, 371284725450756504, 371284724875985851, 371284723877095551, 371284723730337872, 371284723583218924, 371284723433866153]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 34260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 34200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496278802472441, 362496295267402335⟩, ⟨(-397040303218172042), (-396658838380533076)⟩, true⟩

def words07 : List Nat := [371284722964607009, 371284723077595118, 371284724041214968, 371284724042325712, 371284723871763452, 371284723577886055, 371284723700039068, 371284723783176151, 371284724121501466, 371284724460296926]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 34270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 34200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487305761808897, 362487322236767727⟩, ⟨(-89451406717050933), (-89069598035628527)⟩, true⟩

def words08 : List Nat := [371284724803845137, 371284724804956447, 371284724355840917, 371284724557624118, 371284725019270054, 371284725020401518, 371284724923373449, 371284724670714501, 371284724696904474, 371284724773933875]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 34280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 34200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484017452963513, 362484033937931592⟩, ⟨23411349388425265, 23793501338487193⟩, true⟩

def words09 : List Nat := [371284725577100273, 371284726380660861, 371284726972009915, 371284726973126765, 371284726757858922, 371284726744204329, 371284727564989077, 371284727644141732, 371284727644981184, 371284727626017263]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 34290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 34200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 34200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk342
