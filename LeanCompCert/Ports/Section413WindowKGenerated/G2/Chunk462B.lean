import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk462A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk462B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk462A

def state06 : KState := ⟨⟨360554233254121294, 360554246593753761⟩, ⟨1333283305438456978, 1333700308225472190⟩, true⟩

def words05 : List Nat := [360583081395120425, 360583080888515360, 360583080381811044, 360583080103774697, 360583080104309718, 360583079758903150, 360583079413432523, 360583078737649937, 360583077746058233, 360583077123546789]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 46250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 46200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360550569377654982, 360550582723270503⟩, ⟨1502733890768390191, 1503151170361843437⟩, true⟩

def words06 : List Nat := [360583076500845302, 360583076344343928, 360583075721472734, 360583074735598488, 360583073749664546, 360583072541187318, 360583071688582729, 360583070973586503, 360583070258557085, 360583069240892329]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 46260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 46200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360589282894917214, 360589296246521775⟩, ⟨(-288708158166592297), (-288290601430159359)⟩, true⟩

def words07 : List Nat := [360583068539313137, 360583068303831205, 360583068297873598, 360583068378289837, 360583068378875702, 360583068060392224, 360583067741812527, 360583067172240187, 360583066976167806, 360583067111424648]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 46270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 46200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566354094711917, 360566367452357958⟩, ⟨772393961426776244, 772811797792687184⟩, true⟩

def words08 : List Nat := [360583067111990137, 360583067014039282, 360583066586146024, 360583066437751810, 360583066289181867, 360583066022732671, 360583065290377907, 360583064253485258, 360583063216511869, 360583062457711009]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 46280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 46200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360515997911260902, 360516011274895129⟩, ⟨3103595489417504112, 3104013603006458788⟩, true⟩

def words09 : List Nat := [360583062097581306, 360583061532782250, 360583060967940856, 360583060107007336, 360583058910809808, 360583057527320659, 360583056143698849, 360583055089724123, 360583054052763631, 360583052605413628]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 46290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 46200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 46200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk462B
