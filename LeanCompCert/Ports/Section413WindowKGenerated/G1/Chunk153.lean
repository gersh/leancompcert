import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk153

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362458277101559921, 362458280162122979⟩, ⟨392207951277905713, 392239627595213245⟩, true⟩

def state01 : KState := ⟨⟨362420360674009764, 362420363738706878⟩, ⟨972588266266876348, 972620005857119546⟩, true⟩

def words00 : List Nat := [371283915063925142, 371283914543122235, 371283910505304086, 371283906461566983, 371283902418177673, 371283899673843718, 371283894805627129, 371283894199534844, 371283893593379256, 371283892151891537]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 15300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 15300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362561489190693121, 362561492259595610⟩, ⟨(-1188745691109238172), (-1188713887113946854)⟩, true⟩

def words01 : List Nat := [371283888003006353, 371283887330874947, 371283890244348474, 371283891149158313, 371283891365948103, 371283891582857990, 371283894093185751, 371283894903371646, 371283899968788894, 371283905033754350]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 15310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 15300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362493589035592644, 362493592108689809⟩, ⟨(-148493915390234999), (-148462047110814787)⟩, true⟩

def words02 : List Nat := [371283910089189749, 371283910436616491, 371283911404395073, 371283912372273953, 371283914582450600, 371283914582915451, 371283911880798394, 371283909068443993, 371283907695423944, 371283908327650685]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 15320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 15300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476030394619761, 362476033471899386⟩, ⟨121192349090330973, 121224281508187731⟩, true⟩

def words03 : List Nat := [371283913210510536, 371283918092917486, 371283922821635660, 371283924969080526, 371283928402193872, 371283931835097525, 371283936987469471, 371283936987934826, 371283936482104018, 371283935967434470]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 15330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 15300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362503884236854929, 362503887318297693⟩, ⟨(-306168320993797784), (-306136324691933130)⟩, true⟩

def words04 : List Nat := [371283937034068975, 371283937034581339, 371283939326166351, 371283942150349091, 371283944042928090, 371283944043393687, 371283940284653981, 371283939971364689, 371283943583307696, 371283944882971530]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 15340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 15300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362516176594197629, 362516179679894828⟩, ⟨(-495045978992248587), (-495013917363703335)⟩, true⟩

def words05 : List Nat := [371283944883326911, 371283944843378271, 371283947547968318, 371283948173208436, 371283949533555363, 371283950893901628, 371283952247385536, 371283952247859417, 371283952210733904, 371283954309322359]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 15350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 15300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471681343241185, 362471684433085850⟩, ⟨188736655063624726, 188768780418798300⟩, true⟩

def words06 : List Nat := [371283960640543470, 371283961331635475, 371283961903885041, 371283962476209811, 371283963281893270, 371283963282408815, 371283963752368929, 371283964978946581, 371283966070886344, 371283966071369442]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 15360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 15300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362539871088440998, 362539874182504442⟩, ⟨(-859575740049568586), (-859543549830462996)⟩, true⟩

def words07 : List Nat := [371283967506700460, 371283969741003336, 371283976201249888, 371283977029597867, 371283977029959544, 371283976902912764, 371283980872630650, 371283983450805502, 371283987085117270, 371283990719151574]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 15370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 15300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483918195463286, 362483921293737672⟩, ⟨1131295810799767, 1163550815761045⟩, true⟩

def words08 : List Nat := [371283994374142568, 371283994374609338, 371283994653178786, 371283996903255227, 371283999514545458, 371283999515020359, 371283998740560830, 371283997429137852, 371283996897540981, 371283996898079177]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 15380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 15300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362441507968687022, 362441511071176305⟩, ⟨654386139426850387, 654418459320079117⟩, true⟩

def words09 : List Nat := [371284001106160651, 371284005318804865, 371284008718746839, 371284008719214038, 371284007368060604, 371284007291917011, 371284010682547004, 371284010683014161, 371284008535361441, 371284005776326960]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 15390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 15300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 15300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk153
