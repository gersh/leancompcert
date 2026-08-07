import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk252

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360609693221613468, 360609696983871697⟩, ⟨(-652089365905828298), (-652025229034271980)⟩, true⟩

def state01 : KState := ⟨⟨360515744411862729, 360515748177220661⟩, ⟨1715723724161358890, 1715787939161595274⟩, true⟩

def words00 : List Nat := [360583824583384983, 360583824583714409, 360583823606621005, 360583821735058416, 360583819863590802, 360583817417253278, 360583815759213656, 360583813430306190, 360583811101549848, 360583807992340122]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598314248168671, 360598318016637955⟩, ⟨(-366462159397425760), (-366397865944520962)⟩, true⟩

def words01 : List Nat := [360583805292999602, 360583803101140827, 360583800909357974, 360583799399734242, 360583797938296309, 360583795033260157, 360583792128391578, 360583790364364851, 360583789948652821, 360583790525026024]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360538448706682293, 360538452478293174⟩, ⟨1143164428778988601, 1143228801478740199⟩, true⟩

def words02 : List Nat := [360583790525324792, 360583789889680829, 360583787689969184, 360583785718670539, 360583783747441604, 360583781353463434, 360583777395831652, 360583772660349871, 360583767925174056, 360583764757384682]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360492554241363109, 360492558016078642⟩, ⟨2301478240447490279, 2301542691493248419⟩, true⟩

def words03 : List Nat := [360583762961754817, 360583761890597208, 360583760819489296, 360583758766130361, 360583757219229701, 360583754508791786, 360583751798469194, 360583750654424935, 360583747947648031, 360583744335075998]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586172867908223, 360586176645742206⟩, ⟨(-61792149663657354), (-61727619893140522)⟩, true⟩

def words04 : List Nat := [360583740722716023, 360583738051866813, 360583736747876460, 360583736878799263, 360583736879109295, 360583735314916588, 360583733320581542, 360583732891479231, 360583732462319241, 360583732084342930]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk252
