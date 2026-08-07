import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk672

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481330320194613, 362481397125445341⟩, ⟨274074365175948431, 277106426275088519⟩, true⟩

def state01 : KState := ⟨⟨362467878275276575, 362467945100938128⟩, ⟨1178089276360013344, 1181122709171791476⟩, true⟩

def words00 : List Nat := [371285520696711036, 371285520699004309, 371285520429315379, 371285520150454301, 371285519870743461, 371285519659614342, 371285519356281381, 371285519146403006, 371285518935734958, 371285518716607996]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 67200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 67200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362506470550200760, 362506537396549949⟩, ⟨(-1415886045332459540), (-1412851221995872510)⟩, true⟩

def words01 : List Nat := [371285518456694607, 371285518419052877, 371285518560907036, 371285518563240923, 371285518561460384, 371285518524872812, 371285518669274847, 371285518763449659, 371285519077690001, 371285519392920193]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 67210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 67200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486880116112214, 362486946983205000⟩, ⟨(-98950827445392141), (-95914609619681009)⟩, true⟩

def words02 : List Nat := [371285519612616740, 371285519665353716, 371285519863793582, 371285520063429451, 371285520328432256, 371285520330726624, 371285520301064544, 371285520272556234, 371285520316725767, 371285520340590438]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 67220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 67200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362473845779967600, 362473912667727932⟩, ⟨777484376257653708, 780521983668136680⟩, true⟩

def words03 : List Nat := [371285520584327624, 371285520829040454, 371285521074476322, 371285521076770848, 371285521027430443, 371285520958889521, 371285521009258929, 371285521011553697, 371285520838712928, 371285520668674811]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 67230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 67200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474140960927835, 362474207869258928⟩, ⟨757697989724809492, 760736980419107404⟩, true⟩

def words04 : List Nat := [371285520497602023, 371285520489683910, 371285520425373883, 371285520451763308, 371285520453539272, 371285520444300348, 371285520139743944, 371285520057275087, 371285519973597379, 371285519943317205]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 67240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 67200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478669444680733, 362478736373891558⟩, ⟨453158953476681741, 456199348436943465⟩, true⟩

def words05 : List Nat := [371285519776827753, 371285519594426191, 371285519429073101, 371285519431619431, 371285519382621645, 371285519393633759, 371285519395368460, 371285519393680325, 371285519096776421, 371285518998756812]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476308357535348, 362476375307226994⟩, ⟨612003865554205350, 615045638159286564⟩, true⟩

def words06 : List Nat := [371285519019367271, 371285519021674015, 371285518939120483, 371285518812187237, 371285518684356607, 371285518566363089, 371285518343532802, 371285518321545102, 371285518298808091, 371285518248183725]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492987179590651, 362493054150042798⟩, ⟨(-510029217713554305), (-506986048445626457)⟩, true⟩

def words07 : List Nat := [371285518198600433, 371285518286136959, 371285518593133667, 371285518606508621, 371285518608315160, 371285518582857144, 371285518616952037, 371285518619482036, 371285518682976644, 371285518797588976]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481749093626156, 362481816084791770⟩, ⟨246063909281168278, 249108472255833330⟩, true⟩

def words08 : List Nat := [371285518886115997, 371285518888412117, 371285518682496783, 371285518667828197, 371285518701974777, 371285518704277235, 371285518529716335, 371285518312590666, 371285518095432471, 371285518098051628]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479792845356047, 362479859857199236⟩, ⟨377701860356477434, 380747814831431630⟩, true⟩

def words09 : List Nat := [371285518081845035, 371285518121538574, 371285518159356857, 371285518161653375, 371285517905179901, 371285517700917576, 371285517495437751, 371285517492586704, 371285517409948206, 371285517328444874]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk672
