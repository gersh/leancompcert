import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk945A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk945B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk945A

def state06 : KState := ⟨⟨360590872540542268, 360590931541807871⟩, ⟨(-838496901186485014), (-834729537705314452)⟩, true⟩

def words05 : List Nat := [360582103188174683, 360582103241402086, 360582103347272101, 360582103536116859, 360582103696237185, 360582103856611190, 360582103950825803, 360582103952195611, 360582104028213579, 360582104123128867]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594983163439611, 360595042177620031⟩, ⟨(-1227222771364651894), (-1223454186593054098)⟩, true⟩

def words06 : List Nat := [360582104329382020, 360582104502607075, 360582104586639289, 360582104670784054, 360582104726378131, 360582104837939105, 360582104965946497, 360582105094206414, 360582105154006927, 360582105292247211]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602971458748124, 360603030485856324⟩, ⟨(-1982745660924003961), (-1978975853509099717)⟩, true⟩

def words07 : List Nat := [360582105468148244, 360582105644460276, 360582105932115704, 360582106108633006, 360582106182767389, 360582106257001287, 360582106300958000, 360582106431971404, 360582106654309949, 360582106876954863]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595072982400651, 360595132022570121⟩, ⟨(-1235708823454398239), (-1231937780641111819)⟩, true⟩

def words08 : List Nat := [360582107038155083, 360582107163870987, 360582107401061689, 360582107638676281, 360582107847586833, 360582107945342176, 360582107973306926, 360582108001430656, 360582108046146782, 360582108185411818]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583853883419247, 360583912936500211⟩, ⟨(-174466827102265135), (-170694562925967721)⟩, true⟩

def words09 : List Nat := [360582108321603983, 360582108458036713, 360582108538180940, 360582108539551159, 360582108508259293, 360582108449043774, 360582108440408191, 360582108532489992, 360582108552797855, 360582108573301874]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk945B
