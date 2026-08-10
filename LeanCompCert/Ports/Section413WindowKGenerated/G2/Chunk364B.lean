import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364A

def state06 : KState := ⟨⟨360494429718064573, 360494437844617239⟩, ⟨3186957480551723937, 3187157777549427779⟩, true⟩

def words05 : List Nat := [360581867946734344, 360581866917205436, 360581865887677542, 360581864383696401, 360581862768639425, 360581860746216413, 360581858723750994, 360581857452180925, 360581855430372357, 360581853033249972]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 36450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 36400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360537416680320469, 360537424811510003⟩, ⟨1619286855548146056, 1619487321628592442⟩, true⟩

def words06 : List Nat := [360581850636149035, 360581848445594767, 360581846737391673, 360581845007938861, 360581843278548618, 360581840787437567, 360581837546296966, 360581835055787494, 360581832565266029, 360581830825264558]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 36460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 36400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569971055188486, 360569979191049156⟩, ⟨431793231869057390, 431993868329325120⟩, true⟩

def words07 : List Nat := [360581829608131185, 360581828012759180, 360581826417380570, 360581825572342569, 360581825105356102, 360581824438935989, 360581823772507578, 360581822526481521, 360581821452292155, 360581821128229237]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 36470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 36400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591594298005376, 360591602438485000⟩, ⟨(-357063183801365398), (-356862378818062484)⟩, true⟩

def words08 : List Nat := [360581821139661016, 360581821687339421, 360581821856883573, 360581822026480589, 360581822026891321, 360581822365194020, 360581822605075075, 360581822845034029, 360581822845471292, 360581822975636132]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 36480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 36400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360614379138793444, 360614387283914241⟩, ⟨(-1188720839699651293), (-1188519865337363073)⟩, true⟩

def words09 : List Nat := [360581822976041875, 360581822924492498, 360581823570061145, 360581823775367782, 360581823775824521, 360581823333569414, 360581823197767169, 360581824202775764, 360581825095313927, 360581825987913108]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 36490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 36400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 36400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364B
