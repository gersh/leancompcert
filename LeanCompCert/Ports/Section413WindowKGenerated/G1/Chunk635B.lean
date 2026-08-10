import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk635A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk635B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk635A

def state06 : KState := ⟨⟨362490870042654917, 362490929546034358⟩, ⟨(-352990301661922769), (-350435770397572425)⟩, true⟩

def words05 : List Nat := [371285416831887191, 371285416821196848, 371285416897228912, 371285416899389740, 371285416702334806, 371285416465248361, 371285416227317361, 371285416152268631, 371285416079568383, 371285416168799929]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470521819408756, 362470581342257860⟩, ⟨940413372035040055, 942969140891940671⟩, true⟩

def words06 : List Nat := [371285416256308145, 371285416258468780, 371285416050613845, 371285416000708872, 371285415972346859, 371285415974508391, 371285415712358173, 371285415399135128, 371285415085022611, 371285414898037189]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475800571683675, 362475860113966217⟩, ⟨604886249464192980, 607443253803576690⟩, true⟩

def words07 : List Nat := [371285414666164560, 371285414653434015, 371285414639990740, 371285414626330077, 371285414453556672, 371285414356627433, 371285414406473937, 371285414408635138, 371285414260765024, 371285414112925066]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479580514069561, 362479640075702762⟩, ⟨364530034083973956, 367088268838955496⟩, true⟩

def words08 : List Nat := [371285413964152802, 371285413907546120, 371285413726838784, 371285413675085949, 371285413622649034, 371285413526328942, 371285413099699942, 371285412921654671, 371285412809254793, 371285412811492021]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362469132151703960, 362469191733049293⟩, ⟨1028995216243255394, 1031554704590699448⟩, true⟩

def words09 : List Nat := [371285412722340810, 371285412560399866, 371285412413049132, 371285412415453174, 371285412308444751, 371285412189871542, 371285412070587449, 371285411899861678, 371285411398958542, 371285411146643487]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk635B
