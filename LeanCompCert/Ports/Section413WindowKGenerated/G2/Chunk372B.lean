import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk372A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk372B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk372A

def state06 : KState := ⟨⟨360605110491716213, 360605118993929441⟩, ⟨(-879375182537424216), (-879161038116607506)⟩, true⟩

def words05 : List Nat := [360581515688095320, 360581516017117192, 360581517065939440, 360581518667051233, 360581520082245682, 360581521497446089, 360581522374454094, 360581523055368032, 360581523689053234, 360581524322876152]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585123437906351, 360585131944852172⟩, ⟨(-134648309626324357), (-134433988845173627)⟩, true⟩

def words06 : List Nat := [360581524934630947, 360581525139601976, 360581525140049329, 360581524981974229, 360581524823824756, 360581524326527888, 360581524596547348, 360581525001861964, 360581525002313758, 360581525012147250]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604087814514486, 360604096326199272⟩, ⟨(-841645024534399126), (-841430527108408760)⟩, true⟩

def words07 : List Nat := [360581525050647065, 360581525089289798, 360581525846957973, 360581525886748412, 360581525887220086, 360581525237287502, 360581524655987347, 360581525158471168, 360581525764329906, 360581526370267071]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582295751009212, 360582304267484452⟩, ⟨(-29258612810892436), (-29043936773643034)⟩, true⟩

def words08 : List Nat := [360581526431931399, 360581526519696526, 360581526944445473, 360581527369320734, 360581527608550205, 360581527609052693, 360581527340619918, 360581526703487001, 360581526066299132, 360581525421736855]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360538805720037187, 360538814241243158⟩, ⟨1592825475562354462, 1593040328032508508⟩, true⟩

def words09 : List Nat := [360581525961227580, 360581526500785551, 360581526639065504, 360581526639568519, 360581526406405788, 360581525988216548, 360581525569890422, 360581525024155710, 360581524241742029, 360581523097222582]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk372B
