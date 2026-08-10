import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk737A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362500862896169525, 362500943830886671⟩, ⟨(-1157395201901730503), (-1153366958176403339)⟩, true⟩

def state01 : KState := ⟨⟨362489263090095002, 362489344047698883⟩, ⟨(-302497984615378935), (-298468054025564089)⟩, true⟩

def words00 : List Nat := [371285294768332142, 371285294770866066, 371285294833491025, 371285294905525116, 371285295032357131, 371285295034890291, 371285294936721489, 371285294839126204, 371285294824065640, 371285294881983786]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 73700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 73700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474523119809078, 362474604100219056⟩, ⟨784089160900973447, 788120772645301269⟩, true⟩

def words01 : List Nat := [371285295033651238, 371285295186374899, 371285295338695529, 371285295341228755, 371285295248255127, 371285295179185304, 371285295113880476, 371285295116419207, 371285294974493561, 371285294832349351]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 73710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 73700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486063127410405, 362486144130511583⟩, ⟨(-66653096637430350), (-62619811984007360)⟩, true⟩

def words02 : List Nat := [371285294727825568, 371285294730636309, 371285294776448130, 371285294848319311, 371285294888989188, 371285294891523036, 371285294705565628, 371285294704760524, 371285294815369654, 371285294829512221]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 73720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 73700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488732282274551, 362488813308447298⟩, ⟨(-263482191357014447), (-259447205516078369)⟩, true⟩

def words03 : List Nat := [371285294831439352, 371285294807732714, 371285294851625863, 371285294854418237, 371285294865199833, 371285294900516592, 371285294936138481, 371285294938720646, 371285294900054265, 371285294950878021]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 73730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 73700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476698621485786, 362476779670230463⟩, ⟨623952196482145367, 627988846891996023⟩, true⟩

def words04 : List Nat := [371285295142268713, 371285295144803168, 371285295091375895, 371285295030590840, 371285294968816526, 371285294909725891, 371285294773430580, 371285294775301669, 371285294776350218, 371285294773239169]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 73740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 73700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk737A
