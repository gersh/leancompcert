import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk666

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598206130410857, 360598234605176600⟩, ⟨(-1021351887651166150), (-1020070861328944100)⟩, true⟩

def state01 : KState := ⟨⟨360592341478027413, 360592369961632308⟩, ⟨(-630757573403246964), (-629475958348401700)⟩, true⟩

def words00 : List Nat := [360582918911559313, 360582919142559267, 360582919248694146, 360582919354928272, 360582919355733775, 360582919307536824, 360582919505244261, 360582919703126768, 360582919788638199, 360582919931481907]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360609857736086105, 360609886228576224⟩, ⟨(-1797589755720418694), (-1796307548777161646)⟩, true⟩

def words01 : List Nat := [360582920227727303, 360582920524262503, 360582920942386748, 360582921262073127, 360582921389403640, 360582921516809785, 360582921868889302, 360582922334414915, 360582922739930371, 360582923145632751]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597757379981086, 360597785881417300⟩, ⟨(-991575874022659020), (-990293071045320674)⟩, true⟩

def words02 : List Nat := [360582923419481224, 360582923468683781, 360582923594432542, 360582923720451192, 360582923721242902, 360582923690527879, 360582923666014121, 360582923472734337, 360582923309865860, 360582923533995750]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578389003500756, 360578417513807811⟩, ⟨299029371618434415, 300312765703304615⟩, true⟩

def words03 : List Nat := [360582923864562605, 360582924195298462, 360582924342816764, 360582924343756852, 360582924266534385, 360582924133222054, 360582923999627792, 360582924073685655, 360582924074523410, 360582924007890994]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597603607495216, 360597632126666519⟩, ⟨(-981447131489766870), (-980163146647316950)⟩, true⟩

def words04 : List Nat := [360582924046724134, 360582924294475414, 360582924766623839, 360582925238938143, 360582925518872951, 360582925649320167, 360582925774834343, 360582925900607359, 360582926001960319, 360582926223579584]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360598181636008648, 360598210164138515⟩, ⟨(-1019953608512695724), (-1018669026539192706)⟩, true⟩

def words05 : List Nat := [360582926303575002, 360582926383668603, 360582926688203207, 360582927177332080, 360582927609875174, 360582928042558643, 360582928318244782, 360582928369493962, 360582928599504227, 360582928829827011]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585462984307977, 360585491521297822⟩, ⟨(-172170619469194844), (-170885446845318016)⟩, true⟩

def words06 : List Nat := [360582929008659877, 360582929009600405, 360582928963985263, 360582928801804532, 360582928639471044, 360582928391341271, 360582928356664030, 360582928428168334, 360582928429006563, 360582928406197624]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594076727655659, 360594105273525531⟩, ⟨(-746560564886302824), (-745274800187783366)⟩, true⟩

def words07 : List Nat := [360582928406965698, 360582928345886949, 360582928381881668, 360582928514852001, 360582928515735715, 360582928433652281, 360582928351395842, 360582928228559577, 360582928385926222, 360582928554517302]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593819211290917, 360593847766141730⟩, ⟨(-729398370912700919), (-728112007322717059)⟩, true⟩

def words08 : List Nat := [360582928593205876, 360582928751725536, 360582929134462343, 360582929517463693, 360582929843943340, 360582929946165545, 360582929947003830, 360582929936969700, 360582929926769227, 360582930070990620]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360559793588468568, 360559822152176882⟩, ⟨1539964996835175146, 1541251951176603020⟩, true⟩

def words09 : List Nat := [360582930312067216, 360582930553314708, 360582930601838293, 360582930602779301, 360582930426883684, 360582930195063467, 360582929962956186, 360582929955346326, 360582929723294634, 360582929377831704]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk666
