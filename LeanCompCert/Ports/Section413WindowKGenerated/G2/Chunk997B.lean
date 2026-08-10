import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk997A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk997B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk997A

def state06 : KState := ⟨⟨360559420035300397, 360559485976309173⟩, ⟨2285174894282026038, 2289616695519506254⟩, true⟩

def words05 : List Nat := [360582437767978736, 360582437880355022, 360582437928962705, 360582437930413474, 360582437878704675, 360582437789407455, 360582437699686934, 360582437607728666, 360582437454827264, 360582437226264261]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584071799441992, 360584137754142282⟩, ⟨(-174183695014763270), (-169740527844028832)⟩, true⟩

def words06 : List Nat := [360582436997374585, 360582436869350322, 360582436811509081, 360582436819363207, 360582436820715035, 360582436742934896, 360582436589508862, 360582436536927062, 360582436483922940, 360582436452883961]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583393814355423, 360583459782884799⟩, ⟨(-106578941093929920), (-102134394126126138)⟩, true⟩

def words07 : List Nat := [360582436454199100, 360582436395322820, 360582436336172683, 360582436351361198, 360582436352582671, 360582436336092009, 360582436319443346, 360582436246314162, 360582436185377135, 360582436197291088]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573970963278808, 360574036945468585⟩, ⟨833609568273666352, 838055478344844324⟩, true⟩

def words08 : List Nat := [360582436198472393, 360582436199376309, 360582436099954785, 360582435950385355, 360582435800603310, 360582435583086392, 360582435415323391, 360582435348232918, 360582435280977976, 360582435136453101]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584465534823415, 360584531530730529⟩, ⟨(-213668528777273346), (-209221249785728006)⟩, true⟩

def words09 : List Nat := [360582435053468552, 360582435045842203, 360582435128819379, 360582435162694087, 360582435164032584, 360582435112581270, 360582435060854107, 360582435101717196, 360582435123917546, 360582435146427910]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk997B
