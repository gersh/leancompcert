import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk145

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360346512314739129, 360346513499676919⟩, ⟨3382211052117556973, 3382222686907256067⟩, true⟩

def state01 : KState := ⟨⟨360416802878218577, 360416804064862512⟩, ⟨2362818310688339233, 2362829970225667399⟩, true⟩

def words00 : List Nat := [360579754151289617, 360579739553734726, 360579727332932283, 360579719836280690, 360579712340645496, 360579700750747896, 360579684444360984, 360579671247227610, 360579658051859092, 360579645551439057]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 14500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 14500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360496421443831063, 360496422632199816⟩, ⟨1206739952380535384, 1206751636953461626⟩, true⟩

def words01 : List Nat := [360579634329668850, 360579619466389017, 360579604605123355, 360579591852885386, 360579582473001135, 360579571906585379, 360579561341606829, 360579548409653027, 360579537973059698, 360579532249069890]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 14510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 14500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360445307923886002, 360445309113957836⟩, ⟨1948993598969063520, 1949005308279414270⟩, true⟩

def words02 : List Nat := [360579526525808533, 360579522183097025, 360579515123373283, 360579505168672863, 360579495215316504, 360579481942802720, 360579471162183993, 360579463705054910, 360579456248932868, 360579445749076860]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 14520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 14500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360533876200500533, 360533877392285223⟩, ⟨661685118420509648, 661696852626994832⟩, true⟩

def words03 : List Nat := [360579436518157529, 360579427987078130, 360579419457116889, 360579415630152515, 360579411490144006, 360579402987229813, 360579394485450820, 360579390684745849, 360579389246601370, 360579386116674976]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 14530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 14500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360618651662014178, 360618652855524767⟩, ⟨(-571954421510537417), (-571942662200803367)⟩, true⟩

def words04 : List Nat := [360579382987153401, 360579376668949123, 360579369698752572, 360579367427208439, 360579365155927247, 360579361705360088, 360579358421016326, 360579352075530031, 360579345730881627, 360579346782938636]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 14540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 14500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360549152734447070, 360549153929669499⟩, ⟨439858911887920425, 439870696113384325⟩, true⟩

def words05 : List Nat := [360579354177846728, 360579361571773462, 360579364567519362, 360579365717934508, 360579365718086570, 360579364219583777, 360579365913928014, 360579366903841042, 360579366904003079, 360579364829127836]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 14550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 14500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360647809709076748, 360647810906011556⟩, ⟨(-996747374936603448), (-996735565770141676)⟩, true⟩

def words06 : List Nat := [360579365369514927, 360579370433850685, 360579380186315011, 360579389937475816, 360579395649643317, 360579396687677441, 360579397558704199, 360579398429661627, 360579400777767945, 360579405472906750]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 14560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 14500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569151555745223, 360569152754411932⟩, ⟨149587563808521293, 149599398217185391⟩, true⟩

def words07 : List Nat := [360579407834789577, 360579410196366486, 360579411232646106, 360579416032766144, 360579417514158445, 360579418995375800, 360579418995537907, 360579417735716793, 360579414047722274, 360579413344138763]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 14570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 14500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567709316160586, 360567710516542534⟩, ⟨170369441692093307, 170381301117587523⟩, true⟩

def words08 : List Nat := [360579412640592638, 360579411775362031, 360579408935034584, 360579403717973189, 360579398501597727, 360579392111005651, 360579390241049898, 360579390514639499, 360579390514803145, 360579388467270265]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 14580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 14500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360636792241399449, 360636793443498829⟩, ⟨(-837760729527618637), (-837748845036058263)⟩, true⟩

def words09 : List Nat := [360579391535789215, 360579395404184200, 360579403940327609, 360579407821062500, 360579407821233090, 360579407276024746, 360579406879946658, 360579409454872766, 360579413385431110, 360579417315491429]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 14590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 14500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 14500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk145
