import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk614A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493907743133217, 362493963119726774⟩, ⟨(-531361154240090644), (-529064492369703900)⟩, true⟩

def state01 : KState := ⟨⟨362490188490727578, 362490243886100895⟩, ⟨(-303025765664263730), (-300727950622900292)⟩, true⟩

def words00 : List Nat := [371285346690589553, 371285346692685050, 371285346713516281, 371285346858435810, 371285347082233085, 371285347084314817, 371285346954749686, 371285346826419522, 371285346831929621, 371285346914049913]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478386418265423, 362478441832382453⟩, ⟨421801275544746163, 424100241733287497⟩, true⟩

def words01 : List Nat := [371285347091610357, 371285347269977989, 371285347396911798, 371285347398993996, 371285347172432453, 371285347009550190, 371285346945437368, 371285346947556991, 371285346863385747, 371285346753283354]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484612530497990, 362484667963247856⟩, ⟨39412857226405448, 41712967938491768⟩, true⟩

def words02 : List Nat := [371285346696641669, 371285346698938529, 371285346834445779, 371285347022218919, 371285347168600513, 371285347170683264, 371285346963558105, 371285346900446478, 371285346993615708, 371285346995771680]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482104734600877, 362482160186377302⟩, ⟨193508386230036861, 195809665838664559⟩, true⟩

def words03 : List Nat := [371285346986275098, 371285346976787855, 371285347141822038, 371285347187301861, 371285347247090892, 371285347307646853, 371285347366804648, 371285347368903480, 371285347241918135, 371285347192657229]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484428176449538, 362484483646766845⟩, ⟨50782895405271570, 53085314262170322⟩, true⟩

def words04 : List Nat := [371285347355387801, 371285347357472704, 371285347275466954, 371285347194662961, 371285347113082865, 371285347112156319, 371285347209079871, 371285347366651037, 371285347522789455, 371285347524948492]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk614A
