import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk689A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk689B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk689A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk689B
