import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk974A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498239399161651, 362498383829803871⟩, ⟨(-1280316542225195008), (-1270818811659300338)⟩, true⟩

def state01 : KState := ⟨⟨362484018838882166, 362484163300334308⟩, ⟨104822319073603033, 114323050684818173⟩, true⟩

def words00 : List Nat := [371285336678940387, 371285336697267683, 371285336811155580, 371285336926778192, 371285337019285343, 371285337022704275, 371285336987650934, 371285336951729927, 371285336923880753, 371285336927792319]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 97400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 97400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476826550280245, 362476971042523503⟩, ⟨805500991093177821, 815004722219835411⟩, true⟩

def words01 : List Nat := [371285336983857949, 371285337053395901, 371285337119460237, 371285337122880316, 371285337063773188, 371285337038258839, 371285337070955421, 371285337074375277, 371285337011698573, 371285336929633130]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 97410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 97400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487161489857584, 362487306012696890⟩, ⟨(-201347760155828548), (-191841048202447156)⟩, true⟩

def words02 : List Nat := [371285336846079146, 371285336845255002, 371285336863872660, 371285336928495775, 371285336975337804, 371285336978817200, 371285336937669503, 371285336923575199, 371285336995010783, 371285337018760644]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 97420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 97400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489277541596814, 362489422095690036⟩, ⟨(-407542125766644563), (-398032368595097225)⟩, true⟩

def words03 : List Nat := [371285337038863223, 371285337060159161, 371285337117866746, 371285337124417848, 371285337149989928, 371285337176830066, 371285337202272217, 371285337205717280, 371285337194271123, 371285337240561342]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 97430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 97400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481283421401738, 362481428005918930⟩, ⟨371481933528614914, 380994655371655236⟩, true⟩

def words04 : List Nat := [371285337390207020, 371285337413735187, 371285337434995639, 371285337457363993, 371285337510205634, 371285337516590437, 371285337565276415, 371285337615362528, 371285337644809296, 371285337648354761]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 97440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 97400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk974A
