import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk607

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471102945704395, 362471157017766124⟩, ⟨853757741371960795, 855974760525650443⟩, true⟩

def state01 : KState := ⟨⟨362483806118142017, 362483860208603857⟩, ⟨82679166363146154, 84897302497569146⟩, true⟩

def words00 : List Nat := [371285258512719951, 371285258509922724, 371285258531309996, 371285258679426715, 371285258800252011, 371285258802308304, 371285258592763506, 371285258554815735, 371285258613688078, 371285258615826680]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492267725704625, 362492321834943110⟩, ⟨(-431084449519830982), (-428865173364264922)⟩, true⟩

def words01 : List Nat := [371285258594357689, 371285258507888337, 371285258574770982, 371285258595688681, 371285258697468529, 371285258800014653, 371285258870786641, 371285258872879066, 371285258835420469, 371285258954335672]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484485308194060, 362484539435723875⟩, ⟨41514868532320397, 43735255432619479⟩, true⟩

def words02 : List Nat := [371285259275783742, 371285259277840619, 371285259268847039, 371285259257603784, 371285259245607539, 371285259238083679, 371285259274972904, 371285259430679079, 371285259592584186, 371285259594713380]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500824414910852, 362500878561041309⟩, ⟨(-950835375601879728), (-948613858990971238)⟩, true⟩

def words03 : List Nat := [371285259710623555, 371285259839487122, 371285260238620568, 371285260276957531, 371285260278549362, 371285260275635458, 371285260538014146, 371285260686456360, 371285260945003007, 371285261204412493]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489974477595839, 362490028642301540⟩, ⟨(-291802567342262781), (-289579922377147237)⟩, true⟩

def words04 : List Nat := [371285261424462230, 371285261426533674, 371285261521747962, 371285261636118672, 371285261831065856, 371285261833159212, 371285261803968904, 371285261774686135, 371285261892234293, 371285261973071781]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481214743865561, 362481268927134416⟩, ⟨240443757499104536, 242667530268995912⟩, true⟩

def words05 : List Nat := [371285262295124342, 371285262618029918, 371285262843706311, 371285262845765209, 371285262757360696, 371285262717266060, 371285262904759695, 371285262906823306, 371285262860314370, 371285262796954512]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 60750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 60700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362501202147892247, 362501256349586697⟩, ⟨(-974010178943251131), (-971785286541714339)⟩, true⟩

def words06 : List Nat := [371285262938033459, 371285263078296721, 371285263488804466, 371285263900132187, 371285264269466112, 371285264348784999, 371285264538346036, 371285264728996087, 371285265146426229, 371285265411696228]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 60700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362503605379926210, 362503659600337654⟩, ⟨(-1120043409402982290), (-1117817379472665478)⟩, true⟩

def words07 : List Nat := [371285265665062303, 371285265919095808, 371285266443355722, 371285266868846427, 371285267265072688, 371285267662070364, 371285268056164829, 371285268089817361, 371285268393805492, 371285268698913317]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 60770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 60700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488543909603805, 362488598148387484⟩, ⟨(-204546999848991962), (-202319853159191800)⟩, true⟩

def words08 : List Nat := [371285269079031595, 371285269098875973, 371285269117431439, 371285269136710345, 371285269236632697, 371285269244250186, 371285269492474975, 371285269741559684, 371285269969694685, 371285270026574071]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 60780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 60700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505571429693581, 362505625687099100⟩, ⟨(-1239736895265994224), (-1237508616463129050)⟩, true⟩

def words09 : List Nat := [371285270230016294, 371285270434541640, 371285270908849519, 371285271061435851, 371285271157588736, 371285271254318060, 371285271488328329, 371285271588440019, 371285271924608484, 371285272261720190]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 60790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 60700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 60700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk607
