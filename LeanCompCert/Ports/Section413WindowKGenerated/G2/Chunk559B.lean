import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk559A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk559B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk559A

def state06 : KState := ⟨⟨360558745769910489, 360558765595832327⟩, ⟨1289168711955387707, 1289918300785957529⟩, true⟩

def words05 : List Nat := [360581817370541796, 360581817662653602, 360581817794165925, 360581817794944714, 360581817699612319, 360581817427524334, 360581817155221979, 360581816931980725, 360581816727119131, 360581816316003628]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 55950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 55900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360600070825435310, 360600090658708573⟩, ⟨(-1023587129018227462), (-1022837128766059330)⟩, true⟩

def words06 : List Nat := [360581815904726506, 360581815743924921, 360581816004127333, 360581816264567499, 360581816265302017, 360581816214412721, 360581815844925000, 360581815794362537, 360581815919134901, 360581816246445686]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 55960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 55900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585837272624556, 360585857113333434⟩, ⟨(-226788309653950390), (-226037893193972544)⟩, true⟩

def words07 : List Nat := [360581816413253370, 360581816580146420, 360581816991000035, 360581817594050553, 360581818113427301, 360581818632911810, 360581818966206399, 360581819206626971, 360581819279403512, 360581819352428950]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 55970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 55900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597529222816514, 360597549070860907⟩, ⟨(-881484851994906636), (-880734024856044128)⟩, true⟩

def words08 : List Nat := [360581819391885252, 360581819392665655, 360581819287897127, 360581819023581456, 360581818759148185, 360581818414440867, 360581818561552110, 360581818794789598, 360581818867783111, 360581819149536837]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 55980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 55900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360597864893832214, 360597884749242388⟩, ⟨(-900431744590832228), (-899680505005488022)⟩, true⟩

def words09 : List Nat := [360581819407696015, 360581819666071397, 360581819810333868, 360581819811113375, 360581819637296705, 360581819192568266, 360581818747706482, 360581818737592962, 360581819025116874, 360581819312821512]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 55990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 55900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 55900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk559B
