import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk964A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471577446687095, 362471718814959853⟩, ⟨1298402409150333671, 1307603393026875251⟩, true⟩

def state01 : KState := ⟨⟨362484426353527225, 362484567752075808⟩, ⟨59735089580924797, 68938992198817503⟩, true⟩

def words00 : List Nat := [371285283027094450, 371285282997860673, 371285282923104614, 371285282936308256, 371285282938923868, 371285282935579383, 371285282841246793, 371285282800752034, 371285282809169655, 371285282812673245]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489324746436729, 362489466175769242⟩, ⟨(-412560967321714731), (-403354096666644325)⟩, true⟩

def words01 : List Nat := [371285282807827428, 371285282783264380, 371285282819488391, 371285282831800756, 371285282848732632, 371285282866998067, 371285282883593286, 371285282887035044, 371285282868394833, 371285282915933038]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483381718151797, 362483523177585716⟩, ⟨160501346440491224, 169711119630490754⟩, true⟩

def words02 : List Nat := [371285283032395349, 371285283035779333, 371285283028258169, 371285283021489146, 371285283013435019, 371285283004860169, 371285283008452301, 371285283062585206, 371285283115177459, 371285283118679054]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362494023111033549, 362494164601107375⟩, ⟨(-865658880742885973), (-856446152793905473)⟩, true⟩

def words03 : List Nat := [371285283192146336, 371285283285738284, 371285283474308750, 371285283561311857, 371285283629869856, 371285283699425659, 371285283821552362, 371285283891563893, 371285283985985834, 371285284081900877]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490055835589581, 362490197356199578⟩, ⟨(-483078219465061240), (-473862546457911104)⟩, true⟩

def words04 : List Nat := [371285284160044661, 371285284163427358, 371285284137851873, 371285284181806016, 371285284256323274, 371285284259765470, 371285284251740765, 371285284244779508, 371285284314010530, 371285284368812637]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk964A
