import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk815A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362499448238199466, 362499547981678483⟩, ⟨(-1174343576201718194), (-1168854454563503256)⟩, true⟩

def state01 : KState := ⟨⟨362491344189129030, 362491443958119293⟩, ⟨(-513892506296641782), (-508401305368010694)⟩, true⟩

def words00 : List Nat := [371285206534271703, 371285206537093055, 371285206562172371, 371285206642480732, 371285206767553018, 371285206770374748, 371285206714387438, 371285206649963146, 371285206667340591, 371285206747124851]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 81500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 81500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479337204504883, 362479436998883863⟩, ⟨464907070359244097, 470400340854859775⟩, true⟩

def words01 : List Nat := [371285206941646610, 371285207137340953, 371285207332319562, 371285207349979135, 371285207352001113, 371285207348139820, 371285207486096829, 371285207488919284, 371285207433742453, 371285207366166185]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 81510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 81500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480100757792940, 362480200577460642⟩, ⟨402696089797385181, 408191421957579889⟩, true⟩

def words02 : List Nat := [371285207303335017, 371285207306529339, 371285207311803001, 371285207366412945, 371285207398144099, 371285207400966721, 371285207231930854, 371285207214806487, 371285207215305887, 371285207218230391]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 81520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 81500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484050533899358, 362484150379300538⟩, ⟨80670508959625107, 86167939292074519⟩, true⟩

def words03 : List Nat := [371285207158952523, 371285207100322374, 371285207129246295, 371285207153942810, 371285207195941847, 371285207239129362, 371285207281247047, 371285207284070811, 371285207145434179, 371285207135975693]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 81530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 81500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476275427475468, 362476375298050538⟩, ⟨714690923235040766, 720190406375203740⟩, true⟩

def words04 : List Nat := [371285207249094375, 371285207251917659, 371285207177822602, 371285207050500311, 371285206922075088, 371285206826494038, 371285206654573100, 371285206634136066, 371285206612797504, 371285206572193705]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 81540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 81500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk815A
