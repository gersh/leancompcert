import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk729A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk729B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk729A

def state06 : KState := ⟨⟨360588412607733576, 360588447029208862⟩, ⟨(-442316636963557254), (-440620339274740880)⟩, true⟩

def words05 : List Nat := [360582407278539947, 360582407177383496, 360582407161454295, 360582407392977634, 360582407576607904, 360582407760408730, 360582407843987739, 360582407845024439, 360582407823812337, 360582407907770358]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360573371593590729, 360573406024840747⟩, ⟨655078476053989021, 656775486956824511⟩, true⟩

def words06 : List Nat := [360582407983934331, 360582407984971062, 360582407896159403, 360582407652352853, 360582407408379796, 360582407117139111, 360582406920115786, 360582406869241152, 360582406818241397, 360582406648205923]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604992829777124, 360605027270809675⟩, ⟨(-1652462141737057158), (-1650764416954872606)⟩, true⟩

def words07 : List Nat := [360582406525699418, 360582406524510130, 360582406708184185, 360582406924452433, 360582406963618095, 360582407002845376, 360582407229378216, 360582407550660910, 360582407861446455, 360582408172455928]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592243766309683, 360592278217239218⟩, ⟨(-722007069791147102), (-720308622678196162)⟩, true⟩

def words08 : List Nat := [360582408345967062, 360582408599618078, 360582408979857711, 360582409360391005, 360582409619648940, 360582409691724554, 360582409692648642, 360582409671148205, 360582409649464358, 360582409759173454]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580831550662700, 360580866011362335⟩, ⟨111027766054082716, 112726926334265734⟩, true⟩

def words09 : List Nat := [360582410023374074, 360582410287765728, 360582410435395562, 360582410436432708, 360582410396698190, 360582410255952475, 360582410160375245, 360582410234978468, 360582410235911364, 360582410215832668]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk729B
