import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk069

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362589232365744785, 362589232944206782⟩, ⟨(-730392849697355420), (-730390146463312292)⟩, true⟩

def state01 : KState := ⟨⟨362607735907585747, 362607736487789411⟩, ⟨(-857606364171416336), (-857603648910756866)⟩, true⟩

def words00 : List Nat := [371283426112556461, 371283446506036705, 371283465389251565, 371283484267062100, 371283509260112117, 371283523841757789, 371283559367599128, 371283594883234977, 371283625973996542, 371283643932600473]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 6900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 6900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362741286458604700, 362741287040579427⟩, ⟨(-1780654299648516990), (-1780651572141030148)⟩, true⟩

def words01 : List Nat := [371283682819618172, 371283721695490639, 371283776452633395, 371283803403735578, 371283827268613356, 371283851126654574, 371283895875053702, 371283930258587488, 371283967449008359, 371284004628768847]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 6910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 6900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477282164443417, 362477282748189398⟩, ⟨47061544776392046, 47064284550012648⟩, true⟩

def words02 : List Nat := [371284041750082685, 371284051124721862, 371284064413079368, 371284077697694937, 371284097217733350, 371284097217929443, 371284089025073843, 371284080708733981, 371284074131011050, 371284074131241348]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 6920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 6900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362283203534867971, 362283204120374260⟩, ⟨1393674799826566219, 1393677551808434557⟩, true⟩

def words03 : List Nat := [371284086708705521, 371284100262192193, 371284113714348342, 371284113714544546, 371284099529276260, 371284090179851371, 371284080833021552, 371284079792888598, 371284051151689222, 371284022211412940]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 6930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 6900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362447050650227423, 362447051237492800⟩, ⟨255848306960345571, 255851071159252227⟩, true⟩

def words04 : List Nat := [371283993279391854, 371283974698065635, 371283948622902027, 371283939132148436, 371283929644060897, 371283917168189351, 371283883254263772, 371283870048667203, 371283864341053055, 371283864341256722]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 6940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 6900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362510331613120098, 362510332202182152⟩, ⟨(-184509217341931445), (-184506440647228481)⟩, true⟩

def words05 : List Nat := [371283859045318960, 371283849513695041, 371283842941293640, 371283842941510626, 371283838386611181, 371283837510501151, 371283836634580013, 371283835680889036, 371283822655866462, 371283826464407806]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 6950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 6900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362460956236882127, 362460956827698036⟩, ⟨159541255950126663, 159544044860733469⟩, true⟩

def words06 : List Nat := [371283850904914085, 371283850905111126, 371283850146319101, 371283845333668925, 371283840522330073, 371283837463240929, 371283833105464546, 371283841232137317, 371283846934360102, 371283846934564713]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 6960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 6900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362694946522892643, 362694947115492132⟩, ⟨(-1472194053094227590), (-1472191251742848746)⟩, true⟩

def words07 : List Nat := [371283860963745710, 371283878271682808, 371283909995759946, 371283923751207366, 371283935379088292, 371283947003698159, 371283979188730013, 371284001241551886, 371284031463160394, 371284061676193630]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 6970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 6900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362578659498688629, 362578660093070641⟩, ⟨(-660276663497055973), (-660273849694443997)⟩, true⟩

def words08 : List Nat := [371284091724244100, 371284094480847919, 371284117768944459, 371284141050478056, 371284164992438584, 371284172250395072, 371284176798880562, 371284181346128625, 371284200314634436, 371284213826485826]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 6980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 6900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362545189352228585, 362545189948398999⟩, ⟨(-425497219626110417), (-425494393313609079)⟩, true⟩

def words09 : List Nat := [371284247829525879, 371284281822924070, 371284310439661507, 371284320224597000, 371284335823906072, 371284351418852614, 371284387473833812, 371284396349892503, 371284405034840602, 371284413717387200]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 6990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 6900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 6900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk069
