import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk630

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360617278621413811, 360617303988071037⟩, ⟨(-2181832536322976280), (-2180752971272045690)⟩, true⟩

def state01 : KState := ⟨⟨360619295724679948, 360619321099662243⟩, ⟨(-2308886807094769497), (-2307806717521153351)⟩, true⟩

def words00 : List Nat := [360582690186897369, 360582690901981219, 360582691490241760, 360582692078582118, 360582692603206485, 360582693253609683, 360582693897299350, 360582694541131599, 360582695059744071, 360582695641924370]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 63000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 63000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360618823664039720, 360618849047377308⟩, ⟨(-2279127057141843692), (-2278046441060617172)⟩, true⟩

def words01 : List Nat := [360582696195969952, 360582696750254054, 360582697482183784, 360582698225781335, 360582698755891316, 360582699286053433, 360582699818791728, 360582700480366983, 360582701054694187, 360582701629198279]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 63010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 63000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593498050089230, 360593523441869559⟩, ⟨(-683180349294883674), (-682099201110850826)⟩, true⟩

def words02 : List Nat := [360582702010813311, 360582702141685429, 360582702288592347, 360582702435756836, 360582702517125438, 360582702518010813, 360582702348633550, 360582702023166572, 360582701697525052, 360582701795360527]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 63020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 63000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360560880479465996, 360560905879574230⟩, ⟨1372952809621601274, 1374034482756025612⟩, true⟩

def words03 : List Nat := [360582702219229020, 360582702643253639, 360582702940552302, 360582702987197109, 360582702987951091, 360582702862733844, 360582702737252536, 360582702675096394, 360582702456692725, 360582702111851452]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 63030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 63000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582233899608328, 360582259308089658⟩, ⟨26722874600292666, 27805075614600970⟩, true⟩

def words04 : List Nat := [360582701766825371, 360582701451471204, 360582701338890288, 360582701342413172, 360582701343238152, 360582701138229255, 360582700799328570, 360582700637974052, 360582700476376739, 360582700308495917]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 63040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 63000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360583006820459819, 360583032237369517⟩, ⟨(-22046565619307352), (-20963833153960068)⟩, true⟩

def words05 : List Nat := [360582700302290587, 360582700169704837, 360582700036949678, 360582700078974359, 360582700105647461, 360582700132479622, 360582700133268704, 360582700033660399, 360582699793715022, 360582699799996911]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587957198086189, 360587982623350722⟩, ⟨(-334376795184752745), (-333293535823122287)⟩, true⟩

def words06 : List Nat := [360582699914421001, 360582699915306815, 360582699779351407, 360582699406177799, 360582699032871561, 360582698596380106, 360582698320763908, 360582698296453775, 360582698272047736, 360582698205221580]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360627545308506699, 360627570742131537⟩, ⟨(-2831405544010119830), (-2830321757323143446)⟩, true⟩

def words07 : List Nat := [360582698459463238, 360582698713966703, 360582699219266163, 360582699781261127, 360582700123636522, 360582700466072717, 360582700801942271, 360582701263216482, 360582701975243432, 360582702687450680]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585843286695911, 360585868728765476⟩, ⟨(-200715123414002069), (-199630803992176725)⟩, true⟩

def words08 : List Nat := [360582703238480130, 360582703539243260, 360582704051701778, 360582704564420937, 360582704865153265, 360582704915692599, 360582704916484132, 360582704792341931, 360582704668038394, 360582704556316281]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360562743832625222, 360562769283047196⟩, ⟨1256722958118860597, 1257807804536929939⟩, true⟩

def words09 : List Nat := [360582704600855066, 360582704645549742, 360582704646339252, 360582704564802801, 360582704232849753, 360582703837854207, 360582703442604676, 360582703298424363, 360582703160708992, 360582702845718146]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk630
