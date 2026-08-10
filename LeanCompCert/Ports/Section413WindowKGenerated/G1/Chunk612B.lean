import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk612A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk612B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk612A

def state06 : KState := ⟨⟨362484133427876295, 362484188542385417⟩, ⟨67670029666099896, 69950617860147612⟩, true⟩

def words05 : List Nat := [371285329634868512, 371285329616015144, 371285329842027812, 371285329977764863, 371285330192729642, 371285330408518430, 371285330574054463, 371285330576131215, 371285330422954121, 371285330406862403]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484149501531116, 362484204634535369⟩, ⟨66693896521266882, 68975617823580706⟩, true⟩

def words06 : List Nat := [371285330637705664, 371285330639782463, 371285330534248190, 371285330427318907, 371285330319531153, 371285330292673928, 371285330219858027, 371285330309820743, 371285330397310134, 371285330399474550]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502610700163745, 362502665851979083⟩, ⟨(-1064548311023197579), (-1062265437072715305)⟩, true⟩

def words07 : List Nat := [371285330473612649, 371285330567219543, 371285330891058674, 371285330893135854, 371285330862156490, 371285330809643939, 371285330899287379, 371285330946575278, 371285331230864637, 371285331516098913]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486661965276899, 362486717135826622⟩, ⟨(-87174452419719884), (-84890430329318136)⟩, true⟩

def words08 : List Nat := [371285331749051417, 371285331751138747, 371285331973659984, 371285332219909748, 371285332421851762, 371285332423929386, 371285332271067143, 371285332127262394, 371285332071753296, 371285332096745366]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476647727942989, 362476702917210464⟩, ⟨526739541952517438, 529024711349952980⟩, true⟩

def words09 : List Nat := [371285332387154042, 371285332678433844, 371285332968178026, 371285332984130535, 371285332985599279, 371285332982534704, 371285333239138715, 371285333241216741, 371285333148850711, 371285333010380937]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk612B
