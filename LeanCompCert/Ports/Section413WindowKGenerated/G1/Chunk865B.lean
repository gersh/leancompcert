import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk865A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk865B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk865A

def state06 : KState := ⟨⟨362468538811791762, 362468651848742519⟩, ⟨1426341160790438483, 1432947697923017243⟩, true⟩

def words05 : List Nat := [371285206828754754, 371285206861742227, 371285206878503633, 371285206881528563, 371285206770533318, 371285206667807062, 371285206571478071, 371285206574488917, 371285206423094082, 371285206235271205]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476352812523331, 362476465876466332⟩, ⟨749981114995295926, 756589988712902802⟩, true⟩

def words06 : List Nat := [371285206046067404, 371285205991598444, 371285205900095799, 371285205916275043, 371285205918606863, 371285205917190080, 371285205736968970, 371285205646898032, 371285205555276254, 371285205509003157]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484315479819160, 362484428571179730⟩, ⟨60624091226212472, 67235338617805962⟩, true⟩

def words07 : List Nat := [371285205410321549, 371285205312646812, 371285205246173598, 371285205249493279, 371285205244464153, 371285205264000281, 371285205282555240, 371285205285567161, 371285205145335004, 371285205140117335]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474769057401769, 362474882175592788⟩, ⟨887168397554590525, 893781968067994847⟩, true⟩

def words08 : List Nat := [371285205157327552, 371285205160339180, 371285205008970724, 371285204842104681, 371285204674060883, 371285204548011950, 371285204354034678, 371285204294540598, 371285204234081025, 371285204175454990]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488591977780583, 362488705123229651⟩, ⟨(-309824358819475475), (-303208427898542685)⟩, true⟩

def words09 : List Nat := [371285204062620486, 371285204070623704, 371285204165553123, 371285204168567812, 371285204118749690, 371285204037491382, 371285203955071729, 371285203918098556, 371285203867759221, 371285203911605091]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk865B
