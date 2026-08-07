import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk069

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360809239371543462, 360809239620894106⟩, ⟨(-1582559961088936440), (-1582558794100282496)⟩, true⟩

def state01 : KState := ⟨⟨360981456665974642, 360981456916082093⟩, ⟨(-2771415873643453985), (-2771414701429025959)⟩, true⟩

def words00 : List Nat := [360579961495724753, 360580019769258070, 360580063240369711, 360580106698898028, 360580144541181383, 360580192919997804, 360580262102124126, 360580331264239599, 360580383876718415, 360580441910810928]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 6900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 6900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361075115936606282, 361075116187472223⟩, ⟨(-3418700642970627559), (-3418699465511146809)⟩, true⟩

def words01 : List Nat := [360580520727403941, 360580599521218658, 360580688728553941, 360580757396810489, 360580808336135648, 360580859260740355, 360580930937835624, 360581013070469488, 360581084472719764, 360581155854354011]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 6910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 6900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360689585200117978, 360689585451751987⟩, ⟨(-750226066291840695), (-750224883513618675)⟩, true⟩

def words02 : List Nat := [360581216604175350, 360581256867520157, 360581287360648566, 360581317844992449, 360581342490060043, 360581346670687090, 360581346670758804, 360581340296894110, 360581333924854182, 360581343512130920]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 6920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 6900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360241504702113033, 360241504954504947⟩, ⟨2357932648102411820, 2357933836136844106⟩, true⟩

def words03 : List Nat := [360581368726527737, 360581393933666119, 360581408620819377, 360581408620899994, 360581402881646582, 360581386183462895, 360581369490070995, 360581351866295669, 360581313836989160, 360581264873256654]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 6930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 6900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595623938775131, 360595624191928896⟩, ⟨(-101936538932962384), (-101935345607476246)⟩, true⟩

def words04 : List Nat := [360581215923615070, 360581169604727180, 360581137027899992, 360581116293999189, 360581095566061502, 360581057393859379, 360581011759150271, 360580986718981541, 360580961685995510, 360580959345776188]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 6940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 6900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360633315599561009, 360633315853485905⟩, ⟨(-364854123808374040), (-364852925119705394)⟩, true⟩

def words05 : List Nat := [360580959345849348, 360580945154835377, 360580930967887694, 360580928610846116, 360580928610914189, 360580922542684979, 360580916476191977, 360580899919182382, 360580894456106515, 360580901986926545]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 6950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 6900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360703792539548018, 360703792794235739⟩, ⟨(-856189091688555731), (-856187887686813859)⟩, true⟩

def words06 : List Nat := [360580930034884939, 360580943624131126, 360580943624203706, 360580941335020920, 360580939046483470, 360580922884266566, 360580935137460908, 360580951509128100, 360580953785875167, 360580971407392128]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 6960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 6900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360975430851931473, 360975431107385833⟩, ⟨(-2750676076761243997), (-2750674867412180375)⟩, true⟩

def words07 : List Nat := [360581009508685760, 360581047599076104, 360581093589722459, 360581137248555985, 360581163918387492, 360581190580579609, 360581237685060094, 360581295146866411, 360581351613403253, 360581408063780021]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 6970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 6900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360882414880146060, 360882415136374139⟩, ⟨(-2102145066783419599), (-2102143852029872289)⟩, true⟩

def words08 : List Nat := [360581451489376991, 360581474741898289, 360581518407374355, 360581562060372080, 360581591692179949, 360581622254782126, 360581638070555060, 360581653881810862, 360581679249009836, 360581722266680266]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 6980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 6900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360759255267367512, 360759255524363723⟩, ⟨(-1239922292618437086), (-1239921072491879848)⟩, true⟩

def words09 : List Nat := [360581785653723892, 360581849022654567, 360581894894311865, 360581936052496765, 360581971557367724, 360582007052111998, 360582062884433930, 360582098634293732, 360582123942493426, 360582149243476439]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 6990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 6900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 6900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk069
