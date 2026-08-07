import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk054

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362399897461142160, 362399897807293005⟩, ⟨453193465932262598, 453194732591850224⟩, true⟩

def state01 : KState := ⟨⟨362306876451411403, 362306876798891768⟩, ⟨956061232476773766, 956062506322687996⟩, true⟩

def words00 : List Nat := [371283809099465423, 371283809099614594, 371283774661070585, 371283740378161037, 371283706107879343, 371283674545311108, 371283630171417707, 371283619740544641, 371283609313476741, 371283598149413522]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 5400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 5400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362604868372698673, 362604868721530021⟩, ⟨(-658049471527592273), (-658048190365907461)⟩, true⟩

def words01 : List Nat := [371283565489869878, 371283546792176742, 371283543277233778, 371283543277383373, 371283513268660609, 371283479766237072, 371283446612457470, 371283446612626279, 371283457616130131, 371283480012737196]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 5410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 5400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362226530438719100, 362226530788900607⟩, ⟨1393663535630990298, 1393664824117469106⟩, true⟩

def words02 : List Nat := [371283502251165786, 371283502251315524, 371283479413055821, 371283459786577245, 371283440167261045, 371283422561886676, 371283359953907130, 371283294927202454, 371283229924393779, 371283190977504193]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 5420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 5400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362269827553514830, 362269827905052248⟩, ⟨1159548104044127584, 1159549399900016422⟩, true⟩

def words03 : List Nat := [371283143719239745, 371283130128685622, 371283116543080210, 371283103075228157, 371283073585736276, 371283054491815206, 371283049886858167, 371283049887008430, 371283019557740304, 371282980368269163]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 5430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 5400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362527933560149192, 362527933913031005⟩, ⟨(-245290726750080353), (-245289423573635261)⟩, true⟩

def words04 : List Nat := [371282941193134667, 371282935549352733, 371282924139164937, 371282935189678376, 371282936059512514, 371282936059665418, 371282909338324249, 371282903968322208, 371282926679192015, 371282934936040795]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 5440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 5400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362376740037980224, 362376740392235672⟩, ⟨579578810069162223, 579580120738657481⟩, true⟩

def words05 : List Nat := [371282940748869203, 371282946559614881, 371282956365220303, 371282956365387559, 371282953154175533, 371282956724976971, 371282956725090052, 371282955636940718, 371282910042301818, 371282890597499163]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 5450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 5400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362134487689029715, 362134488044627044⟩, ⟨1903957315272927580, 1903958633276297462⟩, true⟩

def words06 : List Nat := [371282877315764069, 371282877315915043, 371282839043997460, 371282800341321186, 371282761652749962, 371282733380745300, 371282688497454377, 371282645950350710, 371282603418756987, 371282560920911560]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 5460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 5400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362616665737904321, 362616666094871770⟩, ⟨(-736014538327590733), (-736013212822880377)⟩, true⟩

def words07 : List Nat := [371282497299578417, 371282466870823283, 371282436453106635, 371282427339869807, 371282400459992402, 371282369653085049, 371282341163876996, 371282341164044645, 371282357114258455, 371282381618896058]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 5470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 5400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362435167610664694, 362435167969002459⟩, ⟨258989329928776827, 258990662949874853⟩, true⟩

def words08 : List Nat := [371282397437443543, 371282397437595124, 371282373877348300, 371282378615486499, 371282393716205798, 371282393716358185, 371282378176414295, 371282360810620889, 371282343451089693, 371282342953146335]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 5480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 5400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362199349614788174, 362199349974490789⟩, ⟨1555436938691975033, 1555438279213188007⟩, true⟩

def words09 : List Nat := [371282340275056522, 371282346186201630, 371282352110116126, 371282352110268094, 371282322739020873, 371282293947223691, 371282265165822972, 371282258687377176, 371282208362975391, 371282156934347733]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 5490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 5400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 5400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk054
