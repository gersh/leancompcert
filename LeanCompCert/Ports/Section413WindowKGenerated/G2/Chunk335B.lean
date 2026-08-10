import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk335A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk335B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk335A

def state06 : KState := ⟨⟨360586768914138261, 360586775752458025⟩, ⟨(-188245616473399540), (-188090448135523884)⟩, true⟩

def words05 : List Nat := [360581177219941939, 360581176947123739, 360581176674188268, 360581176274040664, 360581175502643354, 360581173971814584, 360581172440991915, 360581171313143133, 360581171149844308, 360581171317306048]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581223952740859, 360581230795333594⟩, ⟨(-2419170650136560), (-2263858890209192)⟩, true⟩

def words06 : List Nat := [360581171317712542, 360581170818806539, 360581169739424976, 360581169546172947, 360581169352820502, 360581168510807210, 360581167418269102, 360581165769640736, 360581164121024870, 360581163360378121]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360516392376766539, 360516399223592686⟩, ⟨2174415213619407817, 2174570667515571087⟩, true⟩

def words07 : List Nat := [360581163930686182, 360581164501056718, 360581164519225291, 360581164519674083, 360581163654151905, 360581162210626293, 360581160767055494, 360581160208944549, 360581159063132196, 360581157135073198]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360599974159040914, 360599981010100282⟩, ⟨(-632736915416952084), (-632581319347597294)⟩, true⟩

def words08 : List Nat := [360581155207026988, 360581154164357293, 360581153675772024, 360581152969503035, 360581152263241106, 360581150799817988, 360581149359839392, 360581148805029007, 360581148579765286, 360581149140869012]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593245995636621, 360593252850978862⟩, ⟨(-406769904269382904), (-406614164316854194)⟩, true⟩

def words09 : List Nat := [360581149256954497, 360581149373086266, 360581149463821243, 360581150227665791, 360581150766938086, 360581151306251725, 360581151401577927, 360581151402027033, 360581151238424548, 360581151599101929]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk335B
