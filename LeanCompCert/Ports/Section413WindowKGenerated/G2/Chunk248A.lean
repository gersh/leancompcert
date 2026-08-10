import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk248A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360715355056475473, 360715358695103649⟩, ⟨(-3263373376990929233), (-3263312330938423035)⟩, true⟩

def state01 : KState := ⟨⟨360653652059695646, 360653655701411525⟩, ⟨(-1733317035657585425), (-1733255913014694261)⟩, true⟩

def words00 : List Nat := [360583782877796506, 360583785315700838, 360583788276095261, 360583791236349746, 360583792904246802, 360583793517539059, 360583793517827678, 360583793311518383, 360583794519542609, 360583797335645748]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 24800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 24800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360544156519945619, 360544160164711704⟩, ⟨984070954737976055, 984132153071925545⟩, true⟩

def words01 : List Nat := [360583801133282923, 360583804930675718, 360583807891391484, 360583810166389319, 360583811323017303, 360583812479635344, 360583813312166335, 360583813312490380, 360583812533651940, 360583810936390670]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 24810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 24800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578619354416687, 360578623002246009⟩, ⟨128791196748004093, 128852471126783123⟩, true⟩

def words02 : List Nat := [360583809361382133, 360583810603261464, 360583813000965036, 360583815398537544, 360583816382009973, 360583816382334075, 360583815755141901, 360583814649329668, 360583813543516495, 360583812388920467]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 24820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 24800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573418004368497, 360573421655287213⟩, ⟨257897287866668843, 257958638970384735⟩, true⟩

def words03 : List Nat := [360583812180223987, 360583811007149920, 360583809834109047, 360583809691324203, 360583809691595692, 360583809608526804, 360583809525424572, 360583808323915753, 360583806881330549, 360583806463619355]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 24830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 24800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596905001340071, 360596908655316516⟩, ⟨(-325793892915592771), (-325732465842606857)⟩, true⟩

def words04 : List Nat := [360583807244478316, 360583807244802657, 360583806835145287, 360583805111812844, 360583803388566395, 360583801250805284, 360583800806229294, 360583801392081886, 360583801392375496, 360583801236466466]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 24840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 24800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk248A
