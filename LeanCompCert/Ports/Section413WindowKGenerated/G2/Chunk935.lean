import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk935

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603365551809306, 360603423187173001⟩, ⟨(-2001316338017031007), (-1997677411673735141)⟩, true⟩

def state01 : KState := ⟨⟨360601456532704316, 360601514180952211⟩, ⟨(-1822892790838260823), (-1819252659756582753)⟩, true⟩

def words00 : List Nat := [360582058053226111, 360582058110627759, 360582058282110683, 360582058453987537, 360582058596680781, 360582058742490461, 360582058821120249, 360582058899896052, 360582059012462175, 360582059222072972]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577952698606395, 360578010359614353⟩, ⟨375056840888471700, 378698165227684800⟩, true⟩

def words01 : List Nat := [360582059448467576, 360582059675109368, 360582059807302700, 360582059825556416, 360582059826689454, 360582059794510480, 360582059766971166, 360582059781849778, 360582059783067125, 360582059741192922]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598272992299071, 360598330666082888⟩, ⟨(-1525377810856469107), (-1521735291657846603)⟩, true⟩

def words02 : List Nat := [360582059723706534, 360582059841284790, 360582060072732019, 360582060304433949, 360582060433998227, 360582060478931938, 360582060494821164, 360582060511103215, 360582060641248144, 360582060816603488]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588847088245483, 360588904774920415⟩, ⟨(-643723347142910195), (-640079622175222397)⟩, true⟩

def words03 : List Nat := [360582060934309502, 360582061052161038, 360582061185237068, 360582061422052690, 360582061594936150, 360582061768032390, 360582061868546736, 360582061869900750, 360582061929435362, 360582062004133539]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576023302015032, 360576081001457521⟩, ⟨555802069081893932, 559446988391267498⟩, true⟩

def words04 : List Nat := [360582062035013249, 360582062036367289, 360582061953334887, 360582061813039368, 360582061672516988, 360582061485679696, 360582061356200897, 360582061321236395, 360582061286094626, 360582061193743906]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360600776001750439, 360600833713967294⟩, ⟨(-1759989973162438570), (-1756343858749579178)⟩, true⟩

def words05 : List Nat := [360582061130917029, 360582061107204500, 360582061172102194, 360582061200468544, 360582061201761151, 360582061111321380, 360582061043032068, 360582061130973401, 360582061332715491, 360582061534760685]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360607841092459560, 360607898817591506⟩, ⟨(-2421062298363510632), (-2417414975550255720)⟩, true⟩

def words06 : List Nat := [360582061665087600, 360582061837490082, 360582062123800978, 360582062410519929, 360582062668045615, 360582062907943992, 360582063090291780, 360582063272787804, 360582063452408947, 360582063730058507]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591496262299923, 360591554000183283⟩, ⟨(-891527768293233481), (-887879252266530021)⟩, true⟩

def words07 : List Nat := [360582064099920086, 360582064470033539, 360582064766166421, 360582065073586763, 360582065325497783, 360582065577784973, 360582065819298294, 360582065979405047, 360582066082001043, 360582066184790559]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598590907812595, 360598648658504406⟩, ⟨(-1555482893601551818), (-1551833178897707254)⟩, true⟩

def words08 : List Nat := [360582066401416844, 360582066675446398, 360582066913175806, 360582067151139790, 360582067277407746, 360582067320246177, 360582067347298958, 360582067374752486, 360582067471278321, 360582067649872191]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589233422019073, 360589291185619382⟩, ⟨(-679624261942151255), (-675973339067355883)⟩, true⟩

def words09 : List Nat := [360582067771473879, 360582067893209565, 360582068107832090, 360582068393835516, 360582068650710960, 360582068907802073, 360582069076956084, 360582069168405592, 360582069246666680, 360582069325392811]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk935
