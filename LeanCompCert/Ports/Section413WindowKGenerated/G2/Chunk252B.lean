import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk252A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk252B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk252A

def state06 : KState := ⟨⟨360565340821220680, 360565344602196906⟩, ⟨464477250276886310, 464541859404366114⟩, true⟩

def words05 : List Nat := [360583732084637595, 360583731224276459, 360583731067704325, 360583732847782544, 360583734228118073, 360583735608405973, 360583736196285738, 360583736196615840, 360583735743964478, 360583735016266755]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 25250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 25200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578941636834243, 360578945420922557⟩, ⟨120809105906237014, 120873793660861584⟩, true⟩

def words06 : List Nat := [360583735123944887, 360583735463574025, 360583735463875959, 360583734582481890, 360583733701104146, 360583732097767426, 360583731278169208, 360583730686793770, 360583730095429238, 360583728713113332]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 25260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 25200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585730826572808, 360585734613778467⟩, ⟨(-50789733380970785), (-50724966835838263)⟩, true⟩

def words07 : List Nat := [360583729224473551, 360583729925159777, 360583731810875762, 360583732138648943, 360583732138953800, 360583731103750986, 360583730068572029, 360583728435246799, 360583728087849788, 360583728167560524]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 25270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 25200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360511984200809440, 360511987991163526⟩, ⟨1813677619170836944, 1813742465323454698⟩, true⟩

def words08 : List Nat := [360583728167857674, 360583727371833520, 360583725018521242, 360583723815701893, 360583722612885486, 360583720545671894, 360583717524058464, 360583713713377119, 360583709902936188, 360583705763616016]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 25280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 25200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360461577828897025, 360461581622368649⟩, ⟨3088605458207842110, 3088670383218490182⟩, true⟩

def words09 : List Nat := [360583702928184735, 360583700047788561, 360583697167584211, 360583693499126674, 360583688275088515, 360583682653753051, 360583677032764533, 360583672301192789, 360583668280911967, 360583663455697444]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 25290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 25200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 25200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk252B
