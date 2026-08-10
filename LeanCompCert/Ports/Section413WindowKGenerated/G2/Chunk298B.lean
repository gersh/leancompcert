import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk298A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk298B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk298A

def state06 : KState := ⟨⟨360546938161816549, 360546943522330426⟩, ⟨1089774514662580745, 1089882765097350653⟩, true⟩

def words05 : List Nat := [360583442978098004, 360583443823639243, 360583444032074419, 360583444659714491, 360583444660051503, 360583444498605894, 360583444977451492, 360583444977847292, 360583444502030634, 360583443280036299]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595345444486259, 360595350808744058⟩, ⟨(-355793751249320021), (-355685389003262109)⟩, true⟩

def words06 : List Nat := [360583442058036112, 360583441162212404, 360583442219860520, 360583443307220594, 360583443320526676, 360583443320922686, 360583442879461365, 360583443217249693, 360583443217576528, 360583443427370711]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360601163732179762, 360601169100211933⟩, ⟨(-529585679376977447), (-529477204371865559)⟩, true⟩

def words07 : List Nat := [360583443427726959, 360583443251649681, 360583444015224730, 360583445674466358, 360583446994909664, 360583448315338085, 360583448908167372, 360583448908563515, 360583448979128201, 360583449572606704]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580439077680653, 360580444449450248⟩, ⟨89762544667217289, 89871131365010063⟩, true⟩

def words08 : List Nat := [360583451281682523, 360583452302490268, 360583452437319788, 360583452572177668, 360583452572509588, 360583452575294155, 360583452575619144, 360583452340274903, 360583452104907070, 360583451178502273]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360609879052525428, 360609884428035494⟩, ⟨(-790386187739549969), (-790277489220766695)⟩, true⟩

def words09 : List Nat := [360583451740882835, 360583452403924766, 360583453912326130, 360583454306532423, 360583454306897911, 360583453735665916, 360583453164401811, 360583452858044149, 360583453742364199, 360583454626717118]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk298B
