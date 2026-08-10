import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk898A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475697770985094, 362475819773667890⟩, ⟨828872146513024066, 836269378490589266⟩, true⟩

def state01 : KState := ⟨⟨362485181428598790, 362485303459366095⟩, ⟨(-22804664459804363), (-15404910348765013)⟩, true⟩

def words00 : List Nat := [371285132253426601, 371285132256914701, 371285132202857051, 371285132201499500, 371285132199155436, 371285132177956335, 371285132006032589, 371285131940636191, 371285131928281286, 371285131933491216]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 89800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 89800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476472993726199, 362476595053003222⟩, ⟨759342743767246885, 766745058481366019⟩, true⟩

def words01 : List Nat := [371285131935861428, 371285131922077092, 371285131949836442, 371285131953289367, 371285131936468324, 371285131905757013, 371285131874013443, 371285131823412430, 371285131606624661, 371285131515466832]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 89810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 89800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477658288618722, 362477780375814478⟩, ⟨652884140299126176, 660288962817560354⟩, true⟩

def words02 : List Nat := [371285131451380627, 371285131454514239, 371285131333954403, 371285131213145490, 371285131091036926, 371285131007590686, 371285130878697238, 371285130853499236, 371285130827286944, 371285130803987890]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 89820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 89800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488794240834525, 362488916356423438⟩, ⟨(-347545257138971477), (-340137883923075773)⟩, true⟩

def words03 : List Nat := [371285130724326017, 371285130674569997, 371285130693447528, 371285130696581409, 371285130604172574, 371285130498610252, 371285130391815482, 371285130349706001, 371285130312299638, 371285130358004865]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 89830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 89800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475843032751107, 362475965176575667⟩, ⟨816017817087305782, 823427727141419866⟩, true⟩

def words04 : List Nat := [371285130402311645, 371285130405448584, 371285130315214542, 371285130309014560, 371285130301342807, 371285130276107745, 371285130098855151, 371285129907590865, 371285129715003513, 371285129647662383]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 89840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 89800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk898A
