import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk709A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk709B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk709A

def state06 : KState := ⟨⟨360570806284922601, 360570838773231606⟩, ⟨816947324899354146, 818504502377231464⟩, true⟩

def words05 : List Nat := [360582373797127747, 360582373938408186, 360582373957022124, 360582373958032695, 360582373918192636, 360582373772481517, 360582373677819475, 360582373678828059, 360582373665612950, 360582373504099380]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 70950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 70900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360600730188749030, 360600762686550410⟩, ⟨(-1306648316326197128), (-1305090465222558360)⟩, true⟩

def words06 : List Nat := [360582373342368045, 360582373211970327, 360582373258879763, 360582373337350794, 360582373338289570, 360582373255093753, 360582373238583856, 360582373213329310, 360582373359522667, 360582373619674890]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 70960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 70900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588655738593664, 360588688245995055⟩, ⟨(-449714413627239242), (-448155881164805890)⟩, true⟩

def words07 : List Nat := [360582373752557641, 360582373885552602, 360582374014080749, 360582374241997912, 360582374344756492, 360582374447672866, 360582374448569737, 360582374430952445, 360582374411613005, 360582374501737229]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 70900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580347864167687, 360580380381034251⟩, ⟨140001299857187537, 141560504206440683⟩, true⟩

def words08 : List Nat := [360582374789550980, 360582374879368955, 360582374880281030, 360582374816499457, 360582374752553591, 360582374638852208, 360582374624941891, 360582374606963969, 360582374588877045, 360582374471810508]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 70980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 70900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360624279273323413, 360624311799690874⟩, ⟨(-2978953201793798425), (-2977393322928773201)⟩, true⟩

def words09 : List Nat := [360582374614433965, 360582374785451571, 360582374946677206, 360582375211287773, 360582375306938710, 360582375402665073, 360582375696164389, 360582376089965647, 360582376681423280, 360582377273093661]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 70990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 70900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 70900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk709B
