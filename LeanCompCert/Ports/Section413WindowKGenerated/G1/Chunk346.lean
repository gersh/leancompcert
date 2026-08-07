import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk346

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362465982535454097, 362465999322221616⟩, ⟨650624490744004540, 651017039785567552⟩, true⟩

def state01 : KState := ⟨⟨362507102468682551, 362507119265507911⟩, ⟨(-772309321644474772), (-771916424550894262)⟩, true⟩

def words00 : List Nat := [371284814300592089, 371284814099622167, 371284813827378394, 371284814109769561, 371284814258138375, 371284814259273579, 371284814347497260, 371284814810206425, 371284815987127323, 371284816632687395]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 34600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 34600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362503146261918754, 362503163068948577⟩, ⟨(-635296203834941814), (-634902953511959600)⟩, true⟩

def words01 : List Nat := [371284817285939498, 371284817939525313, 371284819427626071, 371284820504744460, 371284821505900696, 371284822507423053, 371284823353338861, 371284823354463902, 371284823871918983, 371284824403008485]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 34610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 34600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496475837875673, 362496492654917339⟩, ⟨(-404205784902600300), (-403812187917275820)⟩, true⟩

def words02 : List Nat := [371284825655557986, 371284826218632765, 371284826782516069, 371284827346753493, 371284828160117094, 371284828646196210, 371284829834355070, 371284831022898801, 371284831891758993, 371284832229636023]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 34620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 34600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362523540563795530, 362523557391004520⟩, ⟨(-1341514879231210025), (-1341120930101298797)⟩, true⟩

def words03 : List Nat := [371284833401169456, 371284834573245158, 371284836399280933, 371284837114756876, 371284837695255030, 371284838276079856, 371284839466144273, 371284840309075927, 371284841427542720, 371284842546453229]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 34630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 34600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492041338934710, 362492058176301325⟩, ⟨(-250388754336111750), (-249994453295296154)⟩, true⟩

def words04 : List Nat := [371284843660144249, 371284843663725818, 371284843942054278, 371284844220921663, 371284844553818063, 371284844554944815, 371284844041610396, 371284843526507370, 371284843327839183, 371284843537379064]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 34640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 34600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478162502814557, 362478179350276612⟩, ⟨230697158779628741, 231091809679511505⟩, true⟩

def words05 : List Nat := [371284844579440856, 371284845621888752, 371284846661793207, 371284846662917081, 371284846655978709, 371284846720172299, 371284847124774213, 371284847125904829, 371284846933481673, 371284846742361999]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 34650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 34600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481419236117548, 362481436093634223⟩, ⟨117818538924296567, 118213538369076263⟩, true⟩

def words06 : List Nat := [371284846591024874, 371284846592263333, 371284846488649957, 371284846698069957, 371284846773468162, 371284846774592572, 371284845741064966, 371284845540426636, 371284845770531318, 371284845771695056]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 34660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 34600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502523246582046, 362502540114367709⟩, ⟨(-613984437249710315), (-613589081727118515)⟩, true⟩

def words07 : List Nat := [371284845674210731, 371284845429261957, 371284845769642766, 371284845942765620, 371284846308721349, 371284846675073099, 371284847042367197, 371284847043511400, 371284847232866386, 371284847744432381]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 34670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 34600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485106098304746, 362485122976105958⟩, ⟨(-9848349828656734), (-9452646915469684)⟩, true⟩

def words08 : List Nat := [371284848998494133, 371284849145038929, 371284849145885674, 371284849140078419, 371284849161431107, 371284849162682401, 371284849408652404, 371284849948180892, 371284850485840516, 371284850494859656]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 34680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 34600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362525611917004581, 362525628804976283⟩, ⟨(-1415080759611583321), (-1414684703832888311)⟩, true⟩

def words09 : List Nat := [371284851258649101, 371284852022987300, 371284853617886105, 371284854679651993, 371284855605416884, 371284856531479360, 371284857780222251, 371284858616373474, 371284859792084064, 371284860968204061]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 34690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 34600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 34600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk346
