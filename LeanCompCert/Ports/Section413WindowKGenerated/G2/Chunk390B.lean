import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk390A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk390B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk390A

def state06 : KState := ⟨⟨360618777241885917, 360618786621453568⟩, ⟨(-1423176482551020014), (-1422928851582577834)⟩, true⟩

def words05 : List Nat := [360582349140161895, 360582350224302229, 360582351276371908, 360582352741227721, 360582353941067185, 360582355140931293, 360582355960710115, 360582356377657928, 360582357310758881, 360582358244003360]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360568859679462621, 360568869064001238⟩, ⟨526728764498034971, 526976589657791877⟩, true⟩

def words06 : List Nat := [360582359053854033, 360582359211390535, 360582359211861396, 360582358962094084, 360582358712254422, 360582358091276216, 360582357934105854, 360582357760248151, 360582357586346391, 360582357074998367]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360635642260847832, 360635651650372699⟩, ⟨(-2082871521821443561), (-2082623501824142539)⟩, true⟩

def words07 : List Nat := [360582356868616430, 360582357007604167, 360582357525092055, 360582358059050109, 360582358059537714, 360582358033484290, 360582358287325841, 360582358998567547, 360582360362675757, 360582361726833789]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574655733252031, 360574665127811826⟩, ⟨300449620170106373, 300697836957724599⟩, true⟩

def words08 : List Nat := [360582362582966497, 360582362787401882, 360582362787834137, 360582362622157863, 360582362456350376, 360582362125235537, 360582361142447605, 360582359736306457, 360582358330127040, 360582357576953748]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360528914587517117, 360528923987054117⟩, ⟨2088710083617699985, 2088958494988994131⟩, true⟩

def words09 : List Nat := [360582357380600354, 360582357099234701, 360582356817825295, 360582356157789263, 360582355399742173, 360582354195826648, 360582352991812064, 360582352440564637, 360582351401399307, 360582350035519309]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk390B
