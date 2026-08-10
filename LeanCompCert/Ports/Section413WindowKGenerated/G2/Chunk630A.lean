import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk630A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk630A
