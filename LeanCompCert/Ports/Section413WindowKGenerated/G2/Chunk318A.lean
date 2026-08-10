import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk318A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360614204500669302, 360614210613091895⟩, ⟨(-1010646940515274292), (-1010515500643431208)⟩, true⟩

def state01 : KState := ⟨⟨360557321593902328, 360557327710316332⟩, ⟨798306223502616854, 798437790321227832⟩, true⟩

def words00 : List Nat := [360582434761910009, 360582434762333344, 360582434141647049, 360582433027725400, 360582431913804829, 360582430553340282, 360582429807990367, 360582429389772714, 360582428971528439, 360582427923781319]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 31800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 31800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589914748607662, 360589920869016611⟩, ⟨(-238800636359811153), (-238668942442095939)⟩, true⟩

def words01 : List Nat := [360582427135083528, 360582426640611496, 360582426182988324, 360582426183411838, 360582425234221506, 360582423318064136, 360582421401946109, 360582420469785891, 360582420273278102, 360582420509428852]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 31810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 31800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360538146347433967, 360538152471882095⟩, ⟨1408610884741175772, 1408742707205647152⟩, true⟩

def words02 : List Nat := [360582420509806259, 360582420253248908, 360582420031172460, 360582419893919268, 360582419756556252, 360582419084935176, 360582417427598301, 360582415227943229, 360582413028351274, 360582410803870963]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 31820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 31800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360482005455700430, 360482011584136982⟩, ⟨3196075870416906538, 3196207819853027602⟩, true⟩

def words03 : List Nat := [360582409413797644, 360582408762298636, 360582408110797650, 360582406923671042, 360582405607478588, 360582404046016869, 360582402484523266, 360582400808745695, 360582398147970395, 360582394995564527]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 31830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 31800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360539847278006739, 360539853410450736⟩, ⟨1353921694487346955, 1354053771539836381⟩, true⟩

def words04 : List Nat := [360582391843261898, 360582389018899080, 360582386871188553, 360582384699126171, 360582382527168857, 360582379398410058, 360582375285080940, 360582372153643707, 360582369022279185, 360582366872665488]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 31840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 31800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk318A
