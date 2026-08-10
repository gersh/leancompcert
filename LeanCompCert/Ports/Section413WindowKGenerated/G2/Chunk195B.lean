import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk195A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk195B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk195A

def state06 : KState := ⟨⟨360638914368085192, 360638916584429099⟩, ⟨(-1084242991674295485), (-1084213651630562779)⟩, true⟩

def words05 : List Nat := [360583488098601789, 360583485338660709, 360583482578953044, 360583483595927163, 360583484103664166, 360583484611389977, 360583484611614957, 360583483604156091, 360583486438355445, 360583489272347378]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576868243836103, 360576870462535415⟩, ⟨129568667554096248, 129598053681438270⟩, true⟩

def words06 : List Nat := [360583493622451157, 360583495368964839, 360583495806981618, 360583496244981046, 360583496245195159, 360583494392196219, 360583494165092497, 360583494475714385, 360583494475938853, 360583492744276930]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360622730187001237, 360622732408067088⟩, ⟨(-768207030373763580), (-768177597921598756)⟩, true⟩

def words07 : List Nat := [360583494666331873, 360583496926605591, 360583499583992731, 360583499640201778, 360583499640435279, 360583497417422562, 360583495569016448, 360583497635756849, 360583499639781725, 360583501643656609]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360620155919775074, 360620158143222987⟩, ⟨(-718218160212565780), (-718188681107349454)⟩, true⟩

def words08 : List Nat := [360583502058189246, 360583502058439743, 360583500283809733, 360583500694678406, 360583500694888150, 360583500444759880, 360583500324847671, 360583498899239656, 360583497473729773, 360583499030308519]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360513777420193581, 360513779646004587⟩, ⟨1366178116407276437, 1366207641817107569⟩, true⟩

def words09 : List Nat := [360583499897217409, 360583500764083591, 360583500764312673, 360583499602937938, 360583496974504697, 360583493687667537, 360583490401092402, 360583489706662005, 360583487673793804, 360583484117525868]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk195B
