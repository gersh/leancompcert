import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk566A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360599972463620766, 360599992764185373⟩, ⟨(-1031887702680520287), (-1031111400686956183)⟩, true⟩

def state01 : KState := ⟨⟨360610365756467657, 360610386064560659⟩, ⟨(-1620285100389816825), (-1619508372254324985)⟩, true⟩

def words00 : List Nat := [360581775696147995, 360581775958964006, 360581776328398238, 360581776698049968, 360581776988362673, 360581777334934633, 360581777524778882, 360581777714703389, 360581777895972281, 360581778402229057]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 56600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 56600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360565705770876388, 360565726086391656⟩, ⟨908258139278610700, 909035287626212936⟩, true⟩

def words01 : List Nat := [360581779219865799, 360581780037624696, 360581780686481234, 360581781024373187, 360581781169751112, 360581781315344607, 360581781507806126, 360581781508594727, 360581781390111500, 360581781107367040]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 56610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 56600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596754772479674, 360596775095451404⟩, ⟨(-849960906704850703), (-849183336136432311)⟩, true⟩

def words02 : List Nat := [360581780824452485, 360581780778661633, 360581780825496914, 360581780872470530, 360581780873198555, 360581780648925340, 360581780282364824, 360581780019296030, 360581779803500744, 360581780069120659]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 56620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 56600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360568469371390103, 360568489701864077⟩, ⟨752085191571860046, 752863187030248998⟩, true⟩

def words03 : List Nat := [360581780148451267, 360581780227864999, 360581780618550787, 360581781165202209, 360581781583111810, 360581782001135197, 360581782161444313, 360581782162233156, 360581782011687191, 360581781777906278]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 56630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 56600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360566909001826632, 360566929339731209⟩, ⟨840387846427804730, 841166262791727674⟩, true⟩

def words04 : List Nat := [360581781543874772, 360581781402501914, 360581781040201635, 360581780499022518, 360581779957717739, 360581779337647911, 360581778873817508, 360581778588912247, 360581778303931804, 360581777817450393]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 56640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 56600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk566A
