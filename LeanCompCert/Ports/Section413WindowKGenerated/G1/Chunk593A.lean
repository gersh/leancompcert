import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk593A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498704066196101, 362498755577255113⟩, ⟨(-814350591532023624), (-812287240176914006)⟩, true⟩

def state01 : KState := ⟨⟨362485829421570406, 362485880950727694⟩, ⟨(-50892035826255587), (-48827611150006613)⟩, true⟩

def words00 : List Nat := [371285058049157643, 371285058051162830, 371285057929067628, 371285057988594881, 371285058099341475, 371285058101356260, 371285057940863994, 371285057771725496, 371285057687398449, 371285057703587198]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474658536269099, 362474710083524340⟩, ⟨611709392024750608, 613774890184106422⟩, true⟩

def words01 : List Nat := [371285057784650150, 371285057866542325, 371285057915408563, 371285057917414704, 371285057641514963, 371285057451664266, 371285057269856417, 371285057271901433, 371285057101435694, 371285056929279298]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483602115138818, 362483653680337038⟩, ⟨81160413500460349, 83226976127399883⟩, true⟩

def words02 : List Nat := [371285056835747695, 371285056837957893, 371285056859702211, 371285056944114452, 371285056971539500, 371285056973545408, 371285056621879088, 371285056484143153, 371285056458907829, 371285056460989784]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484553019236119, 362484604602710602⟩, ⟨24810580237134349, 26878227285631085⟩, true⟩

def words03 : List Nat := [371285056438846218, 371285056416122854, 371285056652058879, 371285056848746713, 371285057129711498, 371285057411452663, 371285057674551246, 371285057676557797, 371285057560814364, 371285057555647671]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472036327115265, 362472087928466143⟩, ⟨767648582706229082, 769717290632923002⟩, true⟩

def words04 : List Nat := [371285057826097983, 371285057828104765, 371285057727661205, 371285057615753464, 371285057503071546, 371285057386649896, 371285057167611123, 371285057126721268, 371285057085172763, 371285057048780093]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk593A
