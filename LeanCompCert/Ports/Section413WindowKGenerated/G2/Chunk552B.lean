import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk552A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk552B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk552A

def state06 : KState := ⟨⟨360617681126962443, 360617700440353921⟩, ⟨(-1984206398507935195), (-1983485311861523823)⟩, true⟩

def words05 : List Nat := [360581802905020299, 360581803335336931, 360581803815769032, 360581804460575460, 360581804960249486, 360581805460030599, 360581805775654600, 360581806099249450, 360581806749424717, 360581807399839607]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 55250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 55200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599266808868026, 360599286129494883⟩, ⟨(-966560692393003808), (-965839205883005030)⟩, true⟩

def words06 : List Nat := [360581808291201060, 360581808856474931, 360581809221014922, 360581809585627511, 360581809724761415, 360581810066735373, 360581810517256770, 360581810967907762, 360581811201869336, 360581811518833180]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 55260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 55200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611476409389000, 360611495737285806⟩, ⟨(-1641446320313251605), (-1640724431958788225)⟩, true⟩

def words07 : List Nat := [360581811980918863, 360581812443227167, 360581813103577884, 360581813592888344, 360581813749558864, 360581813906281608, 360581814317468631, 360581814945105595, 360581815482655627, 360581816020349449]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 55270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 55200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360618720371401882, 360618739706619778⟩, ⟨(-2042075073406517382), (-2041352780305800414)⟩, true⟩

def words08 : List Nat := [360581816394712523, 360581816526747705, 360581816876249148, 360581817225965634, 360581817493036162, 360581817937222047, 360581818216815506, 360581818496476448, 360581818874120221, 360581819542753945]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 55280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 55200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582056240125709, 360582075582593680⟩, ⟨(-14640884588100966), (-13918190593531384)⟩, true⟩

def words09 : List Nat := [360581820537412884, 360581821532184279, 360581822272641450, 360581822687338883, 360581823019550244, 360581823351962020, 360581823722943046, 360581823891363550, 360581823896600156, 360581823901962344]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 55290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 55200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 55200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk552B
