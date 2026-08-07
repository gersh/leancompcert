import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk689

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

def state06 : KState := ⟨⟨362493436338030869, 362493506830708630⟩, ⟨(-560557629004058204), (-557274512263593512)⟩, true⟩

def words05 : List Nat := [371285424946376394, 371285425054840712, 371285425341910129, 371285425402705646, 371285425429099250, 371285425456205245, 371285425570983500, 371285425582310146, 371285425701107586, 371285425820974671]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483801691052183, 362483872204997273⟩, ⟨103872058825785996, 107156642268742042⟩, true⟩

def words06 : List Nat := [371285425935565598, 371285425937926692, 371285425972114246, 371285426096213185, 371285426258620151, 371285426260978301, 371285426143456163, 371285426009730519, 371285425875031010, 371285425875321599]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473023984166626, 362473094519341943⟩, ⟨847262792680851531, 850548840481683137⟩, true⟩

def words07 : List Nat := [371285425886160795, 371285425920436613, 371285425952861609, 371285425955219959, 371285425707562412, 371285425502547134, 371285425296259111, 371285425241565083, 371285425064279593, 371285424888151478]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482408029807444, 362482478586055459⟩, ⟨199929008116319582, 203216509622961886⟩, true⟩

def words08 : List Nat := [371285424711011715, 371285424643375999, 371285424477912326, 371285424488779148, 371285424490655296, 371285424457634299, 371285424208398337, 371285424147753476, 371285424177317446, 371285424179759228]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479335373205870, 362479405951006356⟩, ⟨411975303205317782, 415264291719087610⟩, true⟩

def words09 : List Nat := [371285424138837303, 371285424078337148, 371285424163344878, 371285424207876242, 371285424315667444, 371285424424338834, 371285424530113197, 371285424532472367, 371285424358346681, 371285424274074749]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk689
