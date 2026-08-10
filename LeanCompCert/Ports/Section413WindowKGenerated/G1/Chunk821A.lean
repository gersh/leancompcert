import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk821A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362500755160228887, 362500856434879085⟩, ⟨(-1287738912959932357), (-1282124540831428741)⟩, true⟩

def state01 : KState := ⟨⟨362485349987220156, 362485451287566147⟩, ⟨(-22957640265271525), (-17341158383324939)⟩, true⟩

def words00 : List Nat := [371285240196887227, 371285240199731132, 371285240227626430, 371285240264613800, 371285240345635322, 371285240348479888, 371285240252492092, 371285240157710822, 371285240090019005, 371285240095906281]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362472532905662504, 362472634231619458⟩, ⟨1029568465937242876, 1035187050869320636⟩, true⟩

def words01 : List Nat := [371285240234720031, 371285240374729181, 371285240505053311, 371285240507898096, 371285240440421797, 371285240380711361, 371285240319560235, 371285240320324895, 371285240166740914, 371285240016457127]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484689418867917, 362484790770294889⟩, ⟨31225072852699867, 36845749510932121⟩, true⟩

def words02 : List Nat := [371285239864893432, 371285239813118763, 371285239686101334, 371285239672363121, 371285239657734718, 371285239626245322, 371285239461326789, 371285239391285095, 371285239394518639, 371285239397465362]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489806803358821, 362489908180707189⟩, ⟨(-389103678979031421), (-383480873264818429)⟩, true⟩

def words03 : List Nat := [371285239394167278, 371285239363176393, 371285239402703231, 371285239421267201, 371285239484128100, 371285239548102919, 371285239581758916, 371285239584654133, 371285239552020022, 371285239612351985]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482462133604386, 362482563536286884⟩, ⟨214249831647004638, 219874718436923392⟩, true⟩

def words04 : List Nat := [371285239819352037, 371285239850937318, 371285239881468023, 371285239912987801, 371285239950526232, 371285239953662369, 371285239953341248, 371285239992648855, 371285240036297441, 371285240039250207]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk821A
