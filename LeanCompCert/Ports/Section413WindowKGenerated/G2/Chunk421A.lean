import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk421A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571203624075908, 360571214587132283⟩, ⟨477204761559074433, 477516683143443349⟩, true⟩

def state01 : KState := ⟨⟨360599028402722885, 360599039371186345⟩, ⟨(-694237211292782815), (-693925062043606479)⟩, true⟩

def words00 : List Nat := [360582557051279147, 360582557633963220, 360582558602835444, 360582559571772450, 360582560006463299, 360582560135413627, 360582560194674208, 360582560254102138, 360582560504242239, 360582560896155033]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 42100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 42100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360553382546181054, 360553393520112228⟩, ⟨1228273787675779432, 1228586167197448732⟩, true⟩

def words01 : List Nat := [360582561004484943, 360582561112877580, 360582561481761281, 360582562130692166, 360582562634741190, 360582563138859739, 360582563311654919, 360582563312228044, 360582562924401716, 360582562232533820]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 42110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 42100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566961849530104, 360566972828857654⟩, ⟨656132615537296762, 656445222381034546⟩, true⟩

def words02 : List Nat := [360582561540499299, 360582561254192635, 360582560407313705, 360582559217327050, 360582558027304041, 360582556666417973, 360582555830725097, 360582555413764531, 360582554996766325, 360582554248804985]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 42120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 42100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585167977217082, 360585178961959214⟩, ⟨(-111087179455559816), (-110774344468464162)⟩, true⟩

def words03 : List Nat := [360582554072224427, 360582554265635298, 360582554266109150, 360582554228895582, 360582553631372323, 360582552547352670, 360582551463274348, 360582550676577994, 360582550239369682, 360582550302352929]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 42130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 42100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360558844893587167, 360558855883788772⟩, ⟨998059788221214571, 998372853297264651⟩, true⟩

def words04 : List Nat := [360582550302867190, 360582549934681133, 360582549321480026, 360582548618077955, 360582547914557576, 360582547066724132, 360582546051854329, 360582544577516386, 360582543103138449, 360582542072479099]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 42140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 42100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk421A
