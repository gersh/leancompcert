import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk195

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360512829450657903, 360512831652818521⟩, ⟨1380047746540943732, 1380076809584522022⟩, true⟩

def state01 : KState := ⟨⟨360556470919756161, 360556473124266814⟩, ⟨528919987614796625, 528949096495999437⟩, true⟩

def words00 : List Nat := [360583601193535429, 360583600182166734, 360583599304737791, 360583596464073342, 360583593623659275, 360583589629860300, 360583586976440591, 360583586939430145, 360583586902400005, 360583584815527501]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 19500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 19500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360621251766044466, 360621253972911034⟩, ⟨(-735428519957862951), (-735399365100853495)⟩, true⟩

def words01 : List Nat := [360583583990926373, 360583584555901818, 360583584556105175, 360583584544173528, 360583584182385150, 360583581583260065, 360583578984348935, 360583577894521330, 360583579824850379, 360583581755037931]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 19510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 19500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360559094483147156, 360559096692397091⟩, ⟨477723874930278159, 477753076322040227⟩, true⟩

def words02 : List Nat := [360583582310669838, 360583582310919667, 360583581442427794, 360583580506719410, 360583579571042780, 360583576735884942, 360583573190308010, 360583567994395191, 360583562798966906, 360583559215506259]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 19520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 19500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360423858239798527, 360423860451400161⟩, ⟨3119934409371417861, 3119963656703905547⟩, true⟩

def words03 : List Nat := [360583559320258715, 360583560677417607, 360583560677640749, 360583560179008416, 360583557069904076, 360583553294600263, 360583549519611677, 360583545679509125, 360583539229825470, 360583531058191559]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 19530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 19500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570416557495845, 360570418771456031⟩, ⟨255489117157456647, 255518410587732437⟩, true⟩

def words04 : List Nat := [360583522887337771, 360583517324139269, 360583513093518620, 360583511469863487, 360583509846350703, 360583505995264941, 360583500905629445, 360583496208429990, 360583491511635564, 360583488766882514]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 19540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 19500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk195
