import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk239A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360672713320061305, 360672716688326941⟩, ⟨(-2164292823160471015), (-2164238361223078785)⟩, true⟩

def state01 : KState := ⟨⟨360631851235941417, 360631854607169347⟩, ⟨(-1187814583992083841), (-1187760051241127935)⟩, true⟩

def words00 : List Nat := [360582169351134037, 360582172705964633, 360582175578055081, 360582178449997348, 360582180137649221, 360582180137960447, 360582180088075221, 360582178915771623, 360582178318598972, 360582180396503080]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 23900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 23900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595260701134174, 360595264075297972⟩, ⟨(-312429904921061285), (-312375301958628889)⟩, true⟩

def words01 : List Nat := [360582184221495973, 360582188046233796, 360582190978650176, 360582193665715818, 360582195900428117, 360582198135035670, 360582202115878544, 360582204360574097, 360582204906831781, 360582205453084912]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 23910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 23900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360701372877228094, 360701376254330439⟩, ⟨(-2851249861601448466), (-2851195188334263828)⟩, true⟩

def words02 : List Nat := [360582206738123603, 360582208922144265, 360582212252085200, 360582215581807106, 360582217175496149, 360582218815708117, 360582221609710504, 360582224403570205, 360582228941499404, 360582233920607057]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 23920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 23900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360628579774241406, 360628583154318596⟩, ⟨(-1108965848492465320), (-1108911104022940268)⟩, true⟩

def words03 : List Nat := [360582238009678192, 360582242098439262, 360582245427525762, 360582249633203066, 360582253387537781, 360582257141612388, 360582259831353887, 360582260788354988, 360582262723543265, 360582264658682535]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 23930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 23900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572719616221580, 360572722999232662⟩, ⟨228587430555945380, 228642245277731378⟩, true⟩

def words04 : List Nat := [360582267810512905, 360582269229877242, 360582269493392690, 360582269756919870, 360582269757180941, 360582270509629869, 360582270514644926, 360582270519713049, 360582270519993717, 360582269648304802]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 23940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 23900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk239A
