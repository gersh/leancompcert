import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk225

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362501749084408090, 362501755931459752⟩, ⟨(-397281770767086321), (-397177593539976791)⟩, true⟩

def state01 : KState := ⟨⟨362478345840979302, 362478352694299748⟩, ⟨129509062593271938, 129613380900703324⟩, true⟩

def words00 : List Nat := [371284107137956651, 371284107267579764, 371284107346937415, 371284107426529216, 371284107606408588, 371284107607190183, 371284108460428204, 371284109732459952, 371284110729150378, 371284110729879522]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 22500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 22500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362505549049855919, 362505555909564727⟩, ⟨(-482809328427120152), (-482704866285878268)⟩, true⟩

def words01 : List Nat := [371284112191836693, 371284113909816191, 371284117279481150, 371284118021989314, 371284118608055805, 371284119194284835, 371284120308305354, 371284120459713004, 371284121412040741, 371284122364593994]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 22510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 22500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362465329642706272, 362465336508773497⟩, ⟨423000232701199347, 423104838067225719⟩, true⟩

def words02 : List Nat := [371284123308706219, 371284123309411253, 371284121628330370, 371284121502678499, 371284121376700790, 371284121366039546, 371284119730736337, 371284118095644644, 371284116460399764, 371284116128749850]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 22520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 22500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362439952320281359, 362439959192701200⟩, ⟨995093607805122237, 995198356327432939⟩, true⟩

def words03 : List Nat := [371284116431060537, 371284117567051436, 371284118045683118, 371284118046390129, 371284116509360614, 371284115570703726, 371284115314135956, 371284115314841743, 371284113695487321, 371284111737347493]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 22530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 22500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494823782189860, 362494830660922735⟩, ⟨(-241838786192732873), (-241733895341920583)⟩, true⟩

def words04 : List Nat := [371284109787579165, 371284109788361929, 371284110528646748, 371284111882698824, 371284112878683363, 371284112879389121, 371284111255820930, 371284110433446281, 371284110753519354, 371284111229618495]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 22540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 22500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362487331336604835, 362487338221772445⟩, ⟨(-72731797725635868), (-72626761739141002)⟩, true⟩

def words05 : List Nat := [371284111697782770, 371284112166148913, 371284114075036783, 371284115298380145, 371284116833324371, 371284118368392954, 371284119895653298, 371284119896359316, 371284118949535303, 371284119093110633]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 22550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 22500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362455629440679301, 362455636332141940⟩, ⟨642544585074319778, 642649763109313426⟩, true⟩

def words06 : List Nat := [371284119502516528, 371284119503223273, 371284117810566357, 371284115980796000, 371284114150925102, 371284112917315146, 371284110707400211, 371284110460703994, 371284110213768768, 371284109959218117]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 22560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 22500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362529662090191443, 362529668988032478⟩, ⟨(-1028699491196766815), (-1028594169169983001)⟩, true⟩

def words07 : List Nat := [371284109398750982, 371284110100107731, 371284112762825051, 371284112812487008, 371284112813044368, 371284112379419138, 371284113216435138, 371284113640241742, 371284115658230700, 371284117676346991]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 22570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 22500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489256591855699, 362489263496081727⟩, ⟨(-116175978429049893), (-116070512195903749)⟩, true⟩

def words08 : List Nat := [371284119707431755, 371284120121489275, 371284121521050530, 371284122920855019, 371284124916005088, 371284124916712961, 371284124828482551, 371284124734101758, 371284125358385413, 371284125586640096]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 22580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 22500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362466162261652604, 362466169172256064⟩, ⟨405774800669481837, 405880411001123297⟩, true⟩

def words09 : List Nat := [371284126543926438, 371284127501422607, 371284128240573431, 371284128241288626, 371284128093778417, 371284128318637028, 371284130100681180, 371284130101388524, 371284129276371348, 371284128482477353]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 22590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 22500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 22500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk225
