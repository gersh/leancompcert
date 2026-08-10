import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk447A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk447B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk447A

def state06 : KState := ⟨⟨360589175797781361, 360589188252485576⟩, ⟨(-269463654787568062), (-269086929058679036)⟩, true⟩

def words05 : List Nat := [360583174934186860, 360583174682560720, 360583174677332150, 360583175177072166, 360583175549250518, 360583175921512180, 360583176042522304, 360583176344652009, 360583176479467141, 360583176614473497]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360579559534526702, 360579571994995089⟩, ⟨160854680656164069, 161231664418108229⟩, true⟩

def words06 : List Nat := [360583176913260683, 360583176913873105, 360583176714538122, 360583176207203991, 360583175699799816, 360583174846940058, 360583174250223120, 360583174026190956, 360583173802101950, 360583173327682561]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360628442703847218, 360628455170102696⟩, ⟨(-2027859893038553900), (-2027482650160207306)⟩, true⟩

def words07 : List Nat := [360583173665617431, 360583174084167061, 360583175000795163, 360583175587347894, 360583175763040334, 360583175938767388, 360583176612593720, 360583177635965719, 360583178647580279, 360583179659279798]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360612760593694510, 360612773065782475⟩, ⟨(-1325827372355548509), (-1325449868269208939)⟩, true⟩

def words08 : List Nat := [360583180221756877, 360583180286525728, 360583180567998891, 360583180849644131, 360583180850159582, 360583180816122316, 360583180806594988, 360583180547007793, 360583180525046678, 360583181186425703]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576361737111563, 360576374214979079⟩, ⟨304685698476956327, 305063461458710345⟩, true⟩

def words09 : List Nat := [360583182179744457, 360583183173140100, 360583183781319115, 360583183891971538, 360583183892486236, 360583183661411890, 360583183696170879, 360583183818051917, 360583183818597906, 360583183667243783]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk447B
