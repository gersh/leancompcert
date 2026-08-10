import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk963A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362495326268874821, 362495467332895865⟩, ⟨(-990092185327431131), (-980920516136381101)⟩, true⟩

def state01 : KState := ⟨⟨362483982557436097, 362484123651540328⟩, ⟨102368567282446762, 111543133640547830⟩, true⟩

def words00 : List Nat := [371285281515024198, 371285281550594816, 371285281583302641, 371285281617213094, 371285281629812318, 371285281633600029, 371285281679949443, 371285281756723860, 371285281815768554, 371285281819265804]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487270449079965, 362487411573803717⟩, ⟨(-214322606044139475), (-205145090569059791)⟩, true⟩

def words01 : List Nat := [371285281852146571, 371285281898828653, 371285281988409110, 371285281991787339, 371285281937899989, 371285281868780662, 371285281798305322, 371285281786447788, 371285281741291123, 371285281767317395]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481106982343993, 362481248137516167⟩, ⟨379341035848693555, 388521484271421021⟩, true⟩

def words02 : List Nat := [371285281781282825, 371285281784670514, 371285281697271510, 371285281710403565, 371285281755073914, 371285281758452512, 371285281659641862, 371285281528216748, 371285281395388065, 371285281372066893]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488031185917318, 362488172371475445⟩, ⟨(-287666621104327390), (-278483245447997540)⟩, true⟩

def words03 : List Nat := [371285281398532715, 371285281468211269, 371285281535870830, 371285281539309590, 371285281527462577, 371285281540659213, 371285281659914182, 371285281705680329, 371285281738216897, 371285281771985633]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483677987712107, 362483819203538019⟩, ⟨131767069892512510, 140953361699434324⟩, true⟩

def words04 : List Nat := [371285281848952233, 371285281873692733, 371285281967850050, 371285282063400931, 371285282140142161, 371285282143521799, 371285282092173436, 371285282094641538, 371285282130615943, 371285282134121304]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk963A
