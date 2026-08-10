import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk292A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk292B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk292A

def state06 : KState := ⟨⟨360583905684309413, 360583910822544629⟩, ⟨(-19403011102342044), (-19301331469599390)⟩, true⟩

def words05 : List Nat := [360583237730625908, 360583241442729158, 360583244288417940, 360583245972685283, 360583247362293546, 360583248751909751, 360583250531622611, 360583251150181635, 360583251173074769, 360583251196029145]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360597282275041152, 360597287416924896⟩, ⟨(-410849273438557929), (-410747487031380583)⟩, true⟩

def words06 : List Nat := [360583251830346675, 360583253054900841, 360583254614459537, 360583256173984521, 360583256730849431, 360583256731236530, 360583256127514765, 360583255151268819, 360583254362645578, 360583254842464462]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564255298365455, 360564260443936821⟩, ⟨556148824202413755, 556250718564483461⟩, true⟩

def words07 : List Nat := [360583254842811697, 360583254437209612, 360583254462979519, 360583256035634843, 360583257295055749, 360583258554455191, 360583259219905729, 360583259220293010, 360583258726174707, 360583258077767576]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566642603447136, 360566647752670456⟩, ⟨486046402904047225, 486148404213690839⟩, true⟩

def words08 : List Nat := [360583257429282283, 360583256448653892, 360583255281775213, 360583253374021686, 360583251466335349, 360583249264697198, 360583247639346748, 360583247177160447, 360583246714958483, 360583245513142074]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360611339110897218, 360611344263775904⟩, ⟨(-823535443011369180), (-823433334618160730)⟩, true⟩

def words09 : List Nat := [360583244946805871, 360583244771100582, 360583244595296143, 360583244586222811, 360583243843148460, 360583242064177046, 360583240285253057, 360583239777084605, 360583240736595655, 360583241696129129]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk292B
