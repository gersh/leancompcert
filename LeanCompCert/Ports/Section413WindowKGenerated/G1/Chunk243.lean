import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk243

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362495024823140438, 362495032861743110⟩, ⟨(-232989557123596585), (-232857482435425977)⟩, true⟩

def state01 : KState := ⟨⟨362497728503315678, 362497736548741887⟩, ⟨(-298719689466841540), (-298587448932412138)⟩, true⟩

def words00 : List Nat := [371285452261662029, 371285452262428227, 371285452077887579, 371285451884609906, 371285451996902721, 371285451997745923, 371285452367739363, 371285453272569317, 371285454053124058, 371285454559151479]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 24300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 24300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362539852440364929, 362539860492727784⟩, ⟨(-1323109204287178733), (-1322976795088172465)⟩, true⟩

def words01 : List Nat := [371285455444817439, 371285456330802310, 371285458441508529, 371285458442274649, 371285458298250104, 371285457911568754, 371285458831710313, 371285459537549775, 371285461774951804, 371285464012521865]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 24310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 24300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473327153725082, 362473335212990164⟩, ⟨294920202446921754, 295052779544538870⟩, true⟩

def words02 : List Nat := [371285465822094500, 371285465822860757, 371285466040388540, 371285466702606007, 371285467418212676, 371285467418979028, 371285465882179734, 371285464134196493, 371285462386040099, 371285462330932809]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 24320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 24300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362453143594427985, 362453151660604861⟩, ⟨786259451340695095, 786392196636668159⟩, true⟩

def words03 : List Nat := [371285462573528140, 371285463314807855, 371285464047343369, 371285464048111098, 371285462945437321, 371285462248177175, 371285462543865904, 371285462544632942, 371285461623046552, 371285460296456820]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 24330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 24300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487900398804910, 362487908471841550⟩, ⟨(-59798291116395055), (-59665378818025255)⟩, true⟩

def words04 : List Nat := [371285459034239907, 371285459035084558, 371285458334555159, 371285458408270856, 371285458408870391, 371285458183483795, 371285456934171390, 371285456988269856, 371285458147481244, 371285458248901301]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 24340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 24300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362496390401070028, 362496398481116603⟩, ⟨(-266589278266938632), (-266456195242221072)⟩, true⟩

def words05 : List Nat := [371285458342629066, 371285458436617504, 371285459114703348, 371285459249520925, 371285459883200843, 371285460517114298, 371285461001325457, 371285461002094473, 371285460212687066, 371285460662667352]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 24350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 24300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362454586494787437, 362454594581664666⟩, ⟨752068859059284482, 752202108515147120⟩, true⟩

def words06 : List Nat := [371285462145295714, 371285462146066794, 371285462031041214, 371285461918357551, 371285461805401104, 371285461797907082, 371285461078688829, 371285460884022525, 371285460689104425, 371285460486815062]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 24360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 24300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362553013967629579, 362553022061441084⟩, ⟨(-1647061099599328460), (-1646927681119886358)⟩, true⟩

def words07 : List Nat := [371285459640796919, 371285460061641617, 371285462168276315, 371285462887541866, 371285463450722237, 371285464014103162, 371285465795750019, 371285466882200142, 371285469653648115, 371285472425203035]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 24370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 24300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362505973839585980, 362505981940346649⟩, ⟨(-500111592152841034), (-499978004218062214)⟩, true⟩

def words08 : List Nat := [371285474824342210, 371285475295998970, 371285477076630261, 371285478857522592, 371285481135141324, 371285481430653029, 371285481431231849, 371285481411693841, 371285482636296844, 371285483477626053]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 24380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 24300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477645552289222, 362477653659970989⟩, ⟨191104168360443244, 191237925136085284⟩, true⟩

def words09 : List Nat := [371285486002443713, 371285488527372368, 371285490978588150, 371285491190092343, 371285491190643791, 371285490975061833, 371285491923993544, 371285491924767465, 371285491600206596, 371285491279853616]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 24390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 24300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 24300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk243
