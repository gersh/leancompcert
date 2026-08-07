import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk138

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493175599652514, 362493178067008900⟩, ⟨(-119063496465457673), (-119040459789846485)⟩, true⟩

def state01 : KState := ⟨⟨362463465793128424, 362463468264178908⟩, ⟨291156563705858820, 291179651379193482⟩, true⟩

def words00 : List Nat := [371284557148305962, 371284557148720526, 371284555750257497, 371284554103175588, 371284552456170859, 371284550939616317, 371284549336096540, 371284551153579013, 371284552959722196, 371284552960151334]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 13800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 13800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362514867856105595, 362514870330903652⟩, ⟨(-419066203064110932), (-419043063617344484)⟩, true⟩

def words01 : List Nat := [371284552031376766, 371284552629379588, 371284557011296873, 371284557011711796, 371284554420692055, 371284550983661156, 371284547890242272, 371284547890707021, 371284548835245304, 371284551029578325]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 13810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 13800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362423873005939005, 362423875484479820⟩, ⟨838622090366064280, 838645281556580276⟩, true⟩

def words02 : List Nat := [371284552565916608, 371284552566331696, 371284547138745989, 371284545313774839, 371284543488858198, 371284541997798840, 371284534749896139, 371284526444677025, 371284518140494721, 371284515056537418]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 13820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 13800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362417569626837029, 362417572109128511⟩, ⟨926077409071997078, 926100652153075676⟩, true⟩

def words03 : List Nat := [371284511506573267, 371284512340994044, 371284512756045507, 371284512756460952, 371284506218961468, 371284501292977044, 371284496367495237, 371284495618985757, 371284491730894766, 371284486896133792]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 13830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 13800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362514494691620412, 362514497177631886⟩, ⟨(-415540587992310471), (-415517293407234495)⟩, true⟩

def words04 : List Nat := [371284482437227617, 371284482437689412, 371284482511435764, 371284484787506173, 371284486604178222, 371284486604601966, 371284487910494900, 371284490601995520, 371284495928579463, 371284498095009171]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 13840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 13800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362518439564192067, 362518442054001839⟩, ⟨(-470284690902539208), (-470261343692445024)⟩, true⟩

def words05 : List Nat := [371284500109701592, 371284502124235475, 371284506256473245, 371284507795154815, 371284509566544695, 371284511337842467, 371284512961178288, 371284512961596648, 371284512663598551, 371284515111956356]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 13850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 13800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362465677009131176, 362465679502641749⟩, ⟨261455706047368003, 261479104570167231⟩, true⟩

def words06 : List Nat := [371284521983362029, 371284523334512853, 371284524678410026, 371284526022256850, 371284528061237268, 371284528061695724, 371284529122978072, 371284530733894204, 371284531636641663, 371284531637073629]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 13860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 13800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362584496197017084, 362584498694298540⟩, ⟨(-1387342427934176101), (-1387318977090111221)⟩, true⟩

def words07 : List Nat := [371284530278255872, 371284529971891029, 371284534543493621, 371284535163540724, 371284535163863989, 371284534560661805, 371284538537026593, 371284540557000192, 371284547758878384, 371284554959906918]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 13870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 13800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362527103052577683, 362527105553627292⟩, ⟨(-590464214912588904), (-590440711747401894)⟩, true⟩

def words08 : List Nat := [371284561233888494, 371284562923577714, 371284569793970588, 371284576663586342, 371284585131843032, 371284587731397359, 371284590304402573, 371284592877188467, 371284597222572737, 371284600283182587]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 13880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 13800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362419756879909111, 362419759384709892⟩, ⟨901409669403563286, 901433224691920734⟩, true⟩

def words09 : List Nat := [371284607168756477, 371284614053504732, 371284619914626891, 371284619915044356, 371284618881583592, 371284618016599549, 371284619701041567, 371284619701459130, 371284615361271257, 371284610695838808]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 13890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 13800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 13800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk138
