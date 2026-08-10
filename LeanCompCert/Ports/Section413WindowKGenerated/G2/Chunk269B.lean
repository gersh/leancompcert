import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk269A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk269B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk269A

def state06 : KState := ⟨⟨360616264709923112, 360616269041474528⟩, ⟨(-908334080539682081), (-908255090401064491)⟩, true⟩

def words05 : List Nat := [360582578674496170, 360582579090875459, 360582580881568474, 360582581301290044, 360582581301619662, 360582580523343233, 360582579745061481, 360582578928371171, 360582580054075379, 360582581303987007]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360622370347297921, 360622374682225210⟩, ⟨(-1073216801759861430), (-1073137720591839044)⟩, true⟩

def words06 : List Nat := [360582581367535591, 360582581844311117, 360582583207838262, 360582584571377901, 360582585578497174, 360582585713971835, 360582585714287796, 360582585015003243, 360582584629147739, 360582586104842398]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360549174197748481, 360549178536020073⟩, ⟨901184504444265404, 901263675824633006⟩, true⟩

def words07 : List Nat := [360582587542655813, 360582588980427675, 360582589541972160, 360582589542326678, 360582588735027532, 360582587115435862, 360582585495860894, 360582584796264508, 360582584654330822, 360582583416517651]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360621596454088196, 360621600795704904⟩, ⟨(-1053130853035374637), (-1053051591386892111)⟩, true⟩

def words08 : List Nat := [360582582311965109, 360582583140055729, 360582584041789318, 360582584943521803, 360582584943854415, 360582584533585982, 360582583281387439, 360582583340922981, 360582584434041627, 360582585879940876]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583789541413060, 360583793886415271⟩, ⟨(-32279532423895428), (-32200179384290142)⟩, true⟩

def words09 : List Nat := [360582586638670675, 360582587397386013, 360582589526046962, 360582592702595176, 360582595524625400, 360582598346505220, 360582600477711114, 360582601242305174, 360582601286770136, 360582601331347523]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk269B
