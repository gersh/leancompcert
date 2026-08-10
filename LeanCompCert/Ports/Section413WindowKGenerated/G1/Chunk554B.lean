import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk554A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk554B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk554A

def state06 : KState := ⟨⟨362517855203972791, 362517900020408176⟩, ⟨(-1828760799306190648), (-1827081740121364800)⟩, true⟩

def words05 : List Nat := [371284953625048081, 371284953764761637, 371284954138120368, 371284954303137391, 371284954415432137, 371284954528329496, 371284954965125892, 371284955287799981, 371284955883094048, 371284956479178820]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362507741097008786, 362507785930288876⟩, ⟨(-1267842406275593215), (-1266162412795998723)⟩, true⟩

def words06 : List Nat := [371284957017503186, 371284957264944595, 371284957764552088, 371284958265123873, 371284958864117661, 371284959030862256, 371284959196434420, 371284959362635798, 371284959852572488, 371284960266197802]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476343324152606, 362476388174251625⟩, ⟨473987679796120961, 475668606306546017⟩, true⟩

def words07 : List Nat := [371284960807438276, 371284961349432830, 371284961802077978, 371284961822494663, 371284961858334966, 371284961895075520, 371284962173752904, 371284962175619771, 371284962021811877, 371284961869390532]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492175599177325, 362492220466019110⟩, ⟨(-404381305030377047), (-402699449547667933)⟩, true⟩

def words08 : List Nat := [371284961861715065, 371284961892844646, 371284962226993255, 371284962561895108, 371284962835887583, 371284962837754783, 371284962843416366, 371284963010007122, 371284963310551848, 371284963443266814]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482515221299647, 362482560105126591⟩, ⟨131782959954358136, 133465758030592246⟩, true⟩

def words09 : List Nat := [371284963561923375, 371284963681188337, 371284964092264262, 371284964342486114, 371284964602671583, 371284964863605335, 371284965114376632, 371284965116244226, 371284964934594672, 371284964893559575]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk554B
