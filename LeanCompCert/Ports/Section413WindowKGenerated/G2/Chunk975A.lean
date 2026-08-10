import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk975A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360591146673130678, 360591209549087800⟩, ⟨(-863429172898046252), (-859289691674600486)⟩, true⟩

def state01 : KState := ⟨⟨360596187700279087, 360596250589580863⟩, ⟨(-1354997541645481542), (-1350856759249932376)⟩, true⟩

def words00 : List Nat := [360582396608551194, 360582396700675337, 360582396711575682, 360582396722618059, 360582396723802782, 360582396744696310, 360582396869864857, 360582396995305356, 360582397067842455, 360582397211405581]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 97500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 97500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602348119055181, 360602411021712264⟩, ⟨(-1955744568063106369), (-1951602483324588431)⟩, true⟩

def words01 : List Nat := [360582397459740463, 360582397708490437, 360582397984203828, 360582398155376544, 360582398225430725, 360582398295572398, 360582398363070212, 360582398483251839, 360582398689611035, 360582398896289796]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 97510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 97500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360601908141920804, 360601971058069880⟩, ⟨(-1912914914526959805), (-1908771513985758419)⟩, true⟩

def words02 : List Nat := [360582399050031363, 360582399099139532, 360582399253067933, 360582399407453509, 360582399515266336, 360582399671550204, 360582399747293957, 360582399823186904, 360582399934604829, 360582400136885993]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 97520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 97500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577659600620293, 360577722530114117⟩, ⟨452171536686342870, 456316238809710824⟩, true⟩

def words03 : List Nat := [360582400336341366, 360582400536044884, 360582400682990853, 360582400725310479, 360582400740826901, 360582400756718731, 360582400788407252, 360582400822613294, 360582400823881742, 360582400777385080]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 97530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 97500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610782878506200, 360610845821365242⟩, ⟨(-2778859814614403271), (-2774713808781707225)⟩, true⟩

def words04 : List Nat := [360582400763578242, 360582400851403151, 360582400988634655, 360582401126133387, 360582401163441453, 360582401218511249, 360582401378328619, 360582401538569425, 360582401803405296, 360582402096454358]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 97540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 97500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk975A
