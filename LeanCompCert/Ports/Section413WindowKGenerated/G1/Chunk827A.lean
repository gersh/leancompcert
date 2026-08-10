import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk827A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497087934463615, 362497190752464479⟩, ⟨(-990433733824717913), (-984692188902592335)⟩, true⟩

def state01 : KState := ⟨⟨362480122079066297, 362480224922946776⟩, ⟨412707931823171743, 418451617122033329⟩, true⟩

def words00 : List Nat := [371285284243851274, 371285284246717460, 371285284281059936, 371285284368651932, 371285284434865292, 371285284437745387, 371285284363976195, 371285284285760217, 371285284206409708, 371285284185637165]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471951354801211, 362472054224552440⟩, ⟨1088604217872986497, 1094350043067938971⟩, true⟩

def words01 : List Nat := [371285284196922017, 371285284270620790, 371285284340603462, 371285284343470133, 371285284218476807, 371285284127844782, 371285284078317017, 371285284081184491, 371285283951353551, 371285283794705583]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362498121473070617, 362498224368460796⟩, ⟨(-1076289780744184057), (-1070541834562762873)⟩, true⟩

def words02 : List Nat := [371285283636720135, 371285283626168123, 371285283624874191, 371285283699439839, 371285283752452412, 371285283755375943, 371285283818013178, 371285283924944294, 371285284176509448, 371285284335890626]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487505450479489, 362487608372007049⟩, ⟨(-197965395845527640), (-192215287187204696)⟩, true⟩

def words03 : List Nat := [371285284460529263, 371285284586106847, 371285284752671754, 371285284847553592, 371285284985954872, 371285285125488890, 371285285254270110, 371285285257139054, 371285285244335295, 371285285275994345]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479490498245301, 362479593445290322⟩, ⟨465271925375275528, 471024145483298444⟩, true⟩

def words04 : List Nat := [371285285427351626, 371285285448986530, 371285285469617176, 371285285491241414, 371285285530281343, 371285285533471916, 371285285523770142, 371285285550979751, 371285285577005930, 371285285579978942]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk827A
