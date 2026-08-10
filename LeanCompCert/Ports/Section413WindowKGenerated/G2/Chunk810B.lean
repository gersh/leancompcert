import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk810A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk810B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk810A

def state06 : KState := ⟨⟨360591548261263581, 360591591103080654⟩, ⟨(-765324533242560470), (-762979144901416570)⟩, true⟩

def words05 : List Nat := [360582176274723274, 360582176634450837, 360582176989972898, 360582177442925665, 360582177782185483, 360582178121623539, 360582178367319764, 360582178461293577, 360582178578357438, 360582178695820672]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583098784375099, 360583141637110899⟩, ⟨(-80395649582676049), (-78049376114576621)⟩, true⟩

def words06 : List Nat := [360582178929509652, 360582179011580153, 360582179016945155, 360582179022426830, 360582179023398763, 360582179003501955, 360582179004457021, 360582178998703551, 360582178992818424, 360582178908439555]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360610146151157968, 360610189014838264⟩, ⟨(-2273296194101161510), (-2270949033307372710)⟩, true⟩

def words07 : List Nat := [360582179073244443, 360582179238397971, 360582179381976626, 360582179529735025, 360582179532844838, 360582179536041580, 360582179690992215, 360582179922387563, 360582180268776028, 360582180615419074]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601775468837066, 360601818343598502⟩, ⟨(-1594680714682378473), (-1592332655378964499)⟩, true⟩

def words08 : List Nat := [360582180818382075, 360582180916097648, 360582181165542165, 360582181415322421, 360582181626817453, 360582181686758031, 360582181687792276, 360582181662876931, 360582181732868726, 360582181976364420]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360599941570833750, 360599984456523784⟩, ⟨(-1445942786833427773), (-1443593841275766571)⟩, true⟩

def words09 : List Nat := [360582182336727191, 360582182697313795, 360582182981733279, 360582183222093292, 360582183353015474, 360582183484225967, 360582183766985963, 360582184064120476, 360582184284651427, 360582184505336058]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk810B
