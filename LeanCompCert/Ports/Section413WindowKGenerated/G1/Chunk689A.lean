import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk689A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497707591921113, 362497777957152413⟩, ⟨(-854679924550078066), (-851405592701906644)⟩, true⟩

def state01 : KState := ⟨⟨362488232855841010, 362488303242356632⟩, ⟨(-201879652687392800), (-198603854244501474)⟩, true⟩

def words00 : List Nat := [371285421143888917, 371285421146245823, 371285421128288379, 371285421226551985, 371285421387896167, 371285421390252511, 371285421294505893, 371285421182002506, 371285421163711303, 371285421208222104]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 68900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 68900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480283282269266, 362480353690001891⟩, ⟨346013128353711472, 349290388969620952⟩, true⟩

def words01 : List Nat := [371285421442097442, 371285421676956886, 371285421915677400, 371285421918033992, 371285421876186132, 371285421810764395, 371285421886152262, 371285421888515469, 371285421816425864, 371285421745558618]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 68910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 68900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362498642275492973, 362498712704358113⟩, ⟨(-919323469320916334), (-916044752144971282)⟩, true⟩

def words02 : List Nat := [371285421762111938, 371285421775973660, 371285421980654183, 371285422186266672, 371285422355915745, 371285422398544761, 371285422650537460, 371285422903779766, 371285423208922565, 371285423404157261]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 68920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 68900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488573324011472, 362488643774342142⟩, ⟨(-225190808452005893), (-221910611547753933)⟩, true⟩

def words03 : List Nat := [371285423567250125, 371285423731096788, 371285424051036982, 371285424266698242, 371285424497436802, 371285424729133326, 371285424918546721, 371285424920904210, 371285424876563282, 371285424926174176]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 68930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 68900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482408139841843, 362482478611186207⟩, ⟨199863720008763986, 203145365706184820⟩, true⟩

def words04 : List Nat := [371285425156627433, 371285425158985001, 371285425109393029, 371285425003772212, 371285424897218267, 371285424855941782, 371285424769369565, 371285424832849196, 371285424879413790, 371285424881899858]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 68940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 68900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk689A
