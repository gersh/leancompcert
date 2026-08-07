import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk172

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362451674049680793, 362451677958099924⟩, ⟨582707947495601041, 582753418583731527⟩, true⟩

def state01 : KState := ⟨⟨362555136438963810, 362555140352100363⟩, ⟨(-1197240895115954242), (-1197195342863965390)⟩, true⟩

def words00 : List Nat := [371285557832868449, 371285557833448821, 371285560163401803, 371285563017600237, 371285565234613356, 371285565235149735, 371285567448478284, 371285570243851678, 371285576415304568, 371285580457680285]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 17200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 17200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362530037176159970, 362530041094103247⟩, ⟨(-765089256453671454), (-765043621453680100)⟩, true⟩

def words01 : List Nat := [371285584486924892, 371285588515876622, 371285593946533778, 371285598105083255, 371285602422875010, 371285606740371124, 371285611061285024, 371285611061812805, 371285613473152188, 371285616053661131]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 17210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 17200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467586990015598, 362467590912658938⟩, ⟨310732817897595853, 310778533857187325⟩, true⟩

def words02 : List Nat := [371285620717593187, 371285621527885833, 371285622327093977, 371285623126391543, 371285624390156396, 371285624716975527, 371285625805184491, 371285626893469798, 371285627971535311, 371285627972081875]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 17220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 17200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362578666767013918, 362578670694436140⟩, ⟨(-1603695335014071732), (-1603649536689997090)⟩, true⟩

def words03 : List Nat := [371285629246355455, 371285631567418176, 371285636315313294, 371285638273079361, 371285639663487227, 371285641053889825, 371285644150412030, 371285646182969152, 371285651579181454, 371285656975006293]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 17230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 17200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362521020867919428, 362521024800116049⟩, ⟨(-609792111095257922), (-609746230436720962)⟩, true⟩

def words04 : List Nat := [371285661674782543, 371285662542244319, 371285666098283146, 371285669654181643, 371285674199023876, 371285674269815559, 371285674331604962, 371285674393586233, 371285677191950943, 371285679241572387]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 17240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 17200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362438003090248242, 362438007027194642⟩, ⟨822911177622319055, 822957140239381623⟩, true⟩

def words05 : List Nat := [371285683494423010, 371285687746989514, 371285691898626891, 371285691899155705, 371285691581447609, 371285690577370402, 371285691924137188, 371285691924666141, 371285689808936439, 371285687046907237]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 17250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 17200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481170522522702, 362481174464211203⟩, ⟨77817854038574655, 77863898528449701⟩, true⟩

def words06 : List Nat := [371285684284969185, 371285683989646903, 371285683817263394, 371285685143024434, 371285685962585888, 371285685963115154, 371285682873756716, 371285682479757908, 371285683085462326, 371285683086013662]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 17260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 17200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485413501138569, 362485417447659390⟩, ⟨4573127259502860, 4619255227069080⟩, true⟩

def words07 : List Nat := [371285682825362522, 371285682297734511, 371285683601329588, 371285683760516115, 371285684970695082, 371285686180940421, 371285687394241139, 371285687394770950, 371285684780471989, 371285684765670216]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 17270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 17200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362447082176734759, 362447086127979429⟩, ⟨667013264208524761, 667059473828704743⟩, true⟩

def words08 : List Nat := [371285686438617016, 371285686439146788, 371285683674142666, 371285680225549117, 371285676777156917, 371285674318316552, 371285670467586491, 371285669351220892, 371285668234806350, 371285666780022732]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 17280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 17200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362531512576929908, 362531516532958755⟩, ⟨(-793139836476962889), (-793093544114076909)⟩, true⟩

def words09 : List Nat := [371285665658540785, 371285666768458297, 371285671218002310, 371285671219897151, 371285671220307633, 371285670723061423, 371285671011974417, 371285671012564076, 371285672974904619, 371285675625258965]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 17290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 17200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 17200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk172
