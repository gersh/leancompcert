import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk764

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488216978422226, 362488304194572901⟩, ⟨(-241358523540542386), (-236858803364844204)⟩, true⟩

def state01 : KState := ⟨⟨362482443421652406, 362482530661545021⟩, ⟨199718438393210958, 204219972575387518⟩, true⟩

def words00 : List Nat := [371285204032110652, 371285204034743395, 371285203849369612, 371285203836515721, 371285203822422515, 371285203790375326, 371285203639750262, 371285203490089040, 371285203344972875, 371285203348007204]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 76400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 76400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471254411426166, 362471341675042107⟩, ⟨1054793277265963963, 1059296624269355135⟩, true⟩

def words01 : List Nat := [371285203422182226, 371285203532428882, 371285203641824343, 371285203644470135, 371285203589591893, 371285203534123204, 371285203507039617, 371285203509678702, 371285203363890085, 371285203185435582]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 76410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 76400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490144477612108, 362490231764790221⟩, ⟨(-388822686716420767), (-384317538971209809)⟩, true⟩

def words02 : List Nat := [371285203005838030, 371285202998441404, 371285203010831437, 371285203104551338, 371285203169574847, 371285203172255310, 371285203168349876, 371285203225467623, 371285203402270773, 371285203470786856]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 76420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 76400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479796319912498, 362479883631152570⟩, ⟨402165553001449974, 406672539917068946⟩, true⟩

def words03 : List Nat := [371285203537501212, 371285203605146032, 371285203724547051, 371285203759438316, 371285203845526115, 371285203932597305, 371285204004573490, 371285204007207624, 371285203850974855, 371285203784735996]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 76430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 76400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472748282534181, 362472835617222707⟩, ⟨940988004090544372, 945496783527429246⟩, true⟩

def words04 : List Nat := [371285203818314616, 371285203820950242, 371285203726692024, 371285203631906656, 371285203536135849, 371285203493706392, 371285203376214399, 371285203303497295, 371285203229860309, 371285203135646873]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 76440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 76400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498432039907599, 362498519398347806⟩, ⟨(-1022661671817938810), (-1018151076442557954)⟩, true⟩

def words05 : List Nat := [371285202975663199, 371285202967323906, 371285203059749238, 371285203062430986, 371285203047382677, 371285203007720447, 371285203070988417, 371285203092386362, 371285203268333702, 371285203445424845]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 76450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 76400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489693641393299, 362489781023650702⟩, ⟨(-354544006726647300), (-350031590169979346)⟩, true⟩

def words06 : List Nat := [371285203562385487, 371285203565020505, 371285203511849069, 371285203573031892, 371285203657701926, 371285203660356946, 371285203627585402, 371285203587397750, 371285203649255037, 371285203712118619]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 76460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 76400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475941634070834, 362476029040067083⟩, ⟨697208745419612047, 701722977404799793⟩, true⟩

def words07 : List Nat := [371285203944607671, 371285204178206922, 371285204402532129, 371285204405167634, 371285204401592226, 371285204388231041, 371285204500932010, 371285204503567607, 371285204405173317, 371285204288202607]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 76470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 76400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478441253251021, 362478528682847580⟩, ⟨506080828619777925, 510596865680164647⟩, true⟩

def words08 : List Nat := [371285204220850086, 371285204223832609, 371285204242871829, 371285204273688869, 371285204276301525, 371285204278937484, 371285204071553051, 371285204036343599, 371285204021544920, 371285204024273651]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 76480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 76400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488754895366680, 362488842348999005⟩, ⟨(-282841323362190815), (-278323447690324027)⟩, true⟩

def words09 : List Nat := [371285203938994584, 371285203856377008, 371285203857995181, 371285203902185678, 371285203997438365, 371285204093783666, 371285204179058756, 371285204181699008, 371285204130717412, 371285204181554262]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 76490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 76400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 76400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk764
