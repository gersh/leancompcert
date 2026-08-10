import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk947A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk947B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk947A

def state06 : KState := ⟨⟨360600872600450257, 360600931861198157⟩, ⟨(-1786494330797941675), (-1782702404726474677)⟩, true⟩

def words05 : List Nat := [360582117677993938, 360582117831443738, 360582118033380828, 360582118257989933, 360582118388154768, 360582118518423780, 360582118641819475, 360582118844528139, 360582119044190633, 360582119244143394]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598565774847005, 360598625048678579⟩, ⟨(-1567988818542103718), (-1564195652599649688)⟩, true⟩

def words06 : List Nat := [360582119388404682, 360582119421814617, 360582119548594907, 360582119675776385, 360582119731252523, 360582119792224043, 360582119793448222, 360582119792297409, 360582119869789379, 360582120045538382]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360578396350950353, 360578455637730040⟩, ⟨343614023386158457, 347408416485902869⟩, true⟩

def words07 : List Nat := [360582120332094870, 360582120618913383, 360582120819968264, 360582120910184147, 360582120927791816, 360582120945769184, 360582121074613977, 360582121092760649, 360582121093995496, 360582121056768719]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583191376922313, 360583250676653761⟩, ⟨(-110865081093635402), (-107069460360383216)⟩, true⟩

def words08 : List Nat := [360582121091808976, 360582121221295083, 360582121335955946, 360582121450870845, 360582121465976486, 360582121467350127, 360582121398740029, 360582121273183763, 360582121147212481, 360582121144732373]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360597625495378230, 360597684808195444⟩, ⟨(-1479166459462323433), (-1475369598266338371)⟩, true⟩

def words09 : List Nat := [360582121145958616, 360582121092622275, 360582121095562560, 360582121252474864, 360582121380786716, 360582121509326685, 360582121581173081, 360582121670901673, 360582121836180413, 360582122001914220]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk947B
