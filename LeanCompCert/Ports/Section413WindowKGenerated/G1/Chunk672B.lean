import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk672A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk672B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk672A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk672B
