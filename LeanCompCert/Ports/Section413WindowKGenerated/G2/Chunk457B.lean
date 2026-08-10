import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk457A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk457B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk457A

def state06 : KState := ⟨⟨360526718048722987, 360526731089812956⟩, ⟨2583941614249754787, 2584344880959204455⟩, true⟩

def words05 : List Nat := [360583213284140440, 360583213171742841, 360583213059269479, 360583212657381650, 360583211778874480, 360583210779244607, 360583209779467632, 360583209256658711, 360583208391565979, 360583207158015736]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 45750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 45700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606540454634768, 360606553501638510⟩, ⟨(-1069136285144579986), (-1068732747791972484)⟩, true⟩

def words06 : List Nat := [360583205924370242, 360583205029836156, 360583204436795366, 360583204320595515, 360583204204356194, 360583203695343358, 360583203203127531, 360583203187747801, 360583203430029388, 360583203940829440]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 45760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 45700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581812711677231, 360581825764663757⟩, ⟨62676298627795347, 63080109841734639⟩, true⟩

def words07 : List Nat := [360583204067411989, 360583204194052487, 360583204194571130, 360583204293668177, 360583204340885179, 360583204388201771, 360583204388760834, 360583204196694271, 360583203690711303, 360583203661340073]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 45770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 45700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360577927494930693, 360577940553824104⟩, ⟨240545813890724217, 240949895552249249⟩, true⟩

def words08 : List Nat := [360583203761175500, 360583203823857796, 360583203824422087, 360583203647734803, 360583203470952853, 360583203186204368, 360583203186721087, 360583203076736809, 360583202966688927, 360583202617496353]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 45780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 45700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598856490769418, 360598869555589059⟩, ⟨(-717953421807486532), (-717549068754776868)⟩, true⟩

def words09 : List Nat := [360583202643596553, 360583202784795959, 360583202810099277, 360583202851957792, 360583202852536947, 360583202464892579, 360583202077145268, 360583202202111544, 360583202544703669, 360583202887421230]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 45790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 45700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 45700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk457B
