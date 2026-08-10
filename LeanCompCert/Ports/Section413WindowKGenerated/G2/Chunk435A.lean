import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk435A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360609483300720017, 360609495036530284⟩, ⟨(-1144276847855185561), (-1143931849231299907)⟩, true⟩

def state01 : KState := ⟨⟨360592612773750782, 360592624515147077⟩, ⟨(-410432092812786301), (-410086851168260139)⟩, true⟩

def words00 : List Nat := [360583199271360417, 360583199659107405, 360583199674785327, 360583199690525964, 360583199691034916, 360583199227158674, 360583199238742914, 360583199451068192, 360583199451597224, 360583199614520379]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605806103291951, 360605817850301983⟩, ⟨(-984583704723450281), (-984238218797286779)⟩, true⟩

def words01 : List Nat := [360583199983796951, 360583200353239956, 360583201076568969, 360583201273658255, 360583201274210893, 360583201016240810, 360583201027176165, 360583201561626156, 360583202081790493, 360583202602058669]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589352757876635, 360589364510543225⟩, ⟨(-268581208598681890), (-268235476471697116)⟩, true⟩

def words02 : List Nat := [360583202807915926, 360583202808510121, 360583202892021145, 360583203118082559, 360583203210126468, 360583203319073587, 360583203319606372, 360583203029231042, 360583202738756913, 360583202569019445]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360537239808735259, 360537251567004224⟩, ⟨2000240976948863359, 2000586952975661923⟩, true⟩

def words03 : List Nat := [360583203091582708, 360583203614235649, 360583203732009368, 360583203732603555, 360583203324536596, 360583202781550796, 360583202238419553, 360583201593429596, 360583200875112706, 360583199820402839]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360565687807307503, 360565699571183779⟩, ⟨761632773093300289, 761978993289871605⟩, true⟩

def words04 : List Nat := [360583198765596400, 360583198238025034, 360583198458144709, 360583198832035920, 360583198832583924, 360583198761784759, 360583198165379990, 360583197555182614, 360583196944841395, 360583196218561274]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk435A
