import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk567A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582354963745262, 360582375339049171⟩, ⟨(-34283220571721082), (-33502684602115914)⟩, true⟩

def state01 : KState := ⟨⟨360569443632758744, 360569464015492281⟩, ⟨697836784083018116, 698617741350686350⟩, true⟩

def words00 : List Nat := [360581784794950650, 360581784806878848, 360581784807582728, 360581784626515745, 360581784445330763, 360581784062414502, 360581783877699862, 360581783684786669, 360581783491800593, 360581783143359513]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 56700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 56700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360619078599842333, 360619098990033408⟩, ⟨(-2117183048604391820), (-2116401668382843992)⟩, true⟩

def words01 : List Nat := [360581783020154296, 360581783114406288, 360581783519011305, 360581783931522602, 360581784094168427, 360581784256873975, 360581784617748844, 360581785184233421, 360581785842734972, 360581786501389294]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 56710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 56700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587766204691967, 360587786602415624⟩, ⟨(-341091093686665040), (-340309286181509552)⟩, true⟩

def words02 : List Nat := [360581786890467885, 360581787058534572, 360581787468742717, 360581787879168946, 360581788208950419, 360581788302353835, 360581788303069811, 360581788156390752, 360581788009553862, 360581787954653704]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 56720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 56700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583211078350690, 360583231483512456⟩, ⟨(-82603405570723899), (-81821176062821507)⟩, true⟩

def words03 : List Nat := [360581788371398420, 360581788788283598, 360581789048999032, 360581789176381743, 360581789177054638, 360581789094102553, 360581789237402565, 360581789419633372, 360581789445752774, 360581789471985292]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 56730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 56700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360609558785387133, 360609579198021034⟩, ⟨(-1577615555688441398), (-1576832902175802052)⟩, true⟩

def words04 : List Nat := [360581789644139434, 360581790056097328, 360581790719581926, 360581791383194923, 360581791762623336, 360581792036879590, 360581792621158956, 360581793205649659, 360581793595401382, 360581794085826081]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 56740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 56700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk567A
