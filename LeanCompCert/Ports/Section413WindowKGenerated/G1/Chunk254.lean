import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk254

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362516094813210626, 362516103628816356⟩, ⟨(-773442587456743578), (-773291200777498484)⟩, true⟩

def state01 : KState := ⟨⟨362481888087412100, 362481896910268593⟩, ⟨95409331500586812, 95560902385856764⟩, true⟩

def words00 : List Nat := [371285661484986092, 371285661485792158, 371285661336629062, 371285661464152852, 371285662062375161, 371285662063177708, 371285660598989704, 371285659107079693, 371285657668969406, 371285657669905975]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 25400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 25400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362436998437227235, 362437007267294506⟩, ⟨1236516669413563314, 1236668423561866848⟩, true⟩

def words01 : List Nat := [371285658920922317, 371285660320143947, 371285661720959312, 371285661721762072, 371285661292674070, 371285660753419435, 371285660314658233, 371285660315461213, 371285658606875839, 371285656693870504]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 25410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 25400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362463313136981521, 362463321974237435⟩, ⟨567566310845937353, 567718247766446047⟩, true⟩

def words02 : List Nat := [371285654780670153, 371285653657216126, 371285651948084816, 371285651784531151, 371285651620722238, 371285651277166378, 371285648874058041, 371285647743458351, 371285646717714615, 371285646718545986]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 25420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 25400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490289777373643, 362490298621969451⟩, ⟨(-118657455636454075), (-118505332026702913)⟩, true⟩

def words03 : List Nat := [371285645841302169, 371285644657547860, 371285643473546265, 371285643424999761, 371285642625329664, 371285642296797512, 371285641968028389, 371285641568659337, 371285640392503153, 371285640576608550]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 25430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 25400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362438254682057874, 362438263533804259⟩, ⟨1205349679121660263, 1205501984680402675⟩, true⟩

def words04 : List Nat := [371285641405892646, 371285641406696430, 371285640179337022, 371285638624799350, 371285637070094196, 371285635580348347, 371285633322540411, 371285632607391093, 371285631892022287, 371285630998821171]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 25440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 25400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362517060164999757, 362517069024021353⟩, ⟨(-800544746075334415), (-800392255326673745)⟩, true⟩

def words05 : List Nat := [371285629138243834, 371285628541200908, 371285628887357862, 371285628942115981, 371285628942738720, 371285628764141347, 371285629946923973, 371285630542842944, 371285631778217341, 371285633013836103]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 25450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 25400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362516691646792384, 362516700513076148⟩, ⟨(-791316443862371469), (-791163768181352629)⟩, true⟩

def words06 : List Nat := [371285634034731641, 371285634035536788, 371285634320778081, 371285635234338526, 371285636219088055, 371285636260468200, 371285636306158919, 371285636352106669, 371285637937820696, 371285639158273379]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 25460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 25400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362494176307165314, 362494185180716112⟩, ⟨(-217538831450603878), (-217385970641907894)⟩, true⟩

def words07 : List Nat := [371285641918219248, 371285644678285998, 371285647135633897, 371285647864646731, 371285649048955414, 371285650233564427, 371285652748877026, 371285653212825528, 371285653548284346, 371285653884038513]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 25470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 25400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490249069897264, 362490257950651218⟩, ⟨(-117280169580643992), (-117127125198965300)⟩, true⟩

def words08 : List Nat := [371285655574522573, 371285656599685778, 371285658591423886, 371285660583324563, 371285662345819518, 371285662346624835, 371285662058886030, 371285661914692329, 371285662927252107, 371285663108346132]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 25480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 25400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362508517570902686, 362508526458986969⟩, ⟨(-583077761336297934), (-582924530067461704)⟩, true⟩

def words09 : List Nat := [371285663214007674, 371285663319924046, 371285664036065162, 371285664198360272, 371285664826408394, 371285665454721760, 371285666098908098, 371285666099721151, 371285666672502729, 371285667569921150]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 25490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 25400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 25400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk254
