import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk243A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk243B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk243A

def state06 : KState := ⟨⟨360603436285479639, 360603439790618349⟩, ⟨(-493784483686484749), (-493726718896825087)⟩, true⟩

def words05 : List Nat := [360583168585066525, 360583168829099035, 360583168829360515, 360583170160884070, 360583171099993587, 360583172039077628, 360583172039360985, 360583171882126090, 360583171862545095, 360583172694895808]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 24350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 24300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360563588731623887, 360563592239751301⟩, ⟨477100418067057960, 477158255676962384⟩, true⟩

def words06 : List Nat := [360583174057035317, 360583174953802515, 360583175004385654, 360583175054996668, 360583175055264412, 360583174010813805, 360583173965772709, 360583173586612224, 360583173207448287, 360583171979417980]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 24360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 24300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360699558082009327, 360699561593136433⟩, ⟨(-2837192946341418417), (-2837135035614283225)⟩, true⟩

def words07 : List Nat := [360583172055156207, 360583172934321316, 360583175495402182, 360583178102470397, 360583179269425472, 360583180436310054, 360583182313898023, 360583185406668079, 360583190180353720, 360583194953719909]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 24370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 24300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360651444914532580, 360651448428692403⟩, ⟨(-1664300396136646731), (-1664242411457252521)⟩, true⟩

def words08 : List Nat := [360583198343615679, 360583200631300237, 360583203865758078, 360583207100043209, 360583209896133975, 360583211597178304, 360583212021867233, 360583212446561118, 360583213807111137, 360583216605009190]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 24380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 24300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582652473965293, 360582655991117394⟩, ⟨14019473528461540, 14077531204580804⟩, true⟩

def words09 : List Nat := [360583221082162411, 360583225559009193, 360583229056791583, 360583230886884228, 360583230980609722, 360583231074406754, 360583232143339317, 360583232962148469, 360583232962434456, 360583232939117582]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 24390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 24300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 24300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk243B
