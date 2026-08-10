import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk572A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362506987076321294, 362507034866520970⟩, ⟨(-1263864707745056329), (-1262018121935839881)⟩, true⟩

def state01 : KState := ⟨⟨362489819825656502, 362489867633239166⟩, ⟨(-281849288727121663), (-280001708519923033)⟩, true⟩

def words00 : List Nat := [371284972362095057, 371284972374399339, 371284972692009101, 371284973010647133, 371284973360481117, 371284973362410210, 371284973304902363, 371284973246700778, 371284973351917858, 371284973439665904]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 57200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 57200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473806216792632, 362473854041742952⟩, ⟨634362973039443815, 636211546939625465⟩, true⟩

def words01 : List Nat := [371284973563282705, 371284973687630094, 371284973798502125, 371284973800431507, 371284973503897150, 371284973300493479, 371284973115380740, 371284973117344493, 371284972925749882, 371284972733580415]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 57210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 57200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362507552215109607, 362507600057330013⟩, ⟨(-1296693163435693979), (-1294843601255231763)⟩, true⟩

def words02 : List Nat := [371284972651965834, 371284972675380350, 371284973003618440, 371284973332649480, 371284973593850454, 371284973626518096, 371284973925862032, 371284974226178709, 371284974795830593, 371284975193161028]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 57220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 57200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487600526461614, 362487648386323514⟩, ⟨(-154683480710406176), (-152832908821604624)⟩, true⟩

def words03 : List Nat := [371284975591440900, 371284975990407242, 371284976508164061, 371284976874887456, 371284977332981010, 371284977791780597, 371284978248645229, 371284978299058605, 371284978347049002, 371284978396127298]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 57230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 57200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479575977356294, 362479623854409573⟩, ⟨304722848422653857, 306574404435064611⟩, true⟩

def words04 : List Nat := [371284978749521011, 371284978751451407, 371284978698098980, 371284978644152474, 371284978616475404, 371284978618642236, 371284978670250185, 371284978766588447, 371284978863839865, 371284978865840754]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 57240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 57200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk572A
