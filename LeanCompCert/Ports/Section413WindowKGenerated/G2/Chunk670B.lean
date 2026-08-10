import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk670A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk670B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk670A

def state06 : KState := ⟨⟨360578761602129332, 360578790487352712⟩, ⟨275657729393702963, 276966186699080179⟩, true⟩

def words05 : List Nat := [360582919619093242, 360582919963945969, 360582920135310355, 360582920242959449, 360582920294677754, 360582920346652364, 360582920620283288, 360582920672156979, 360582920673008064, 360582920612415329]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 67050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 67000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588947485274581, 360588976379430786⟩, ⟨(-407389458435876593), (-406080402051972391)⟩, true⟩

def words06 : List Nat := [360582920711929888, 360582920984702123, 360582921440843410, 360582921897152541, 360582922137520660, 360582922156072218, 360582922156860020, 360582921989810089, 360582921822475414, 360582921893855024]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 67060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 67000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606534961412330, 360606563864582655⟩, ⟨(-1587095431129471859), (-1585785770124334497)⟩, true⟩

def words07 : List Nat := [360582921894698631, 360582921864459024, 360582922024687417, 360582922387493488, 360582922692077944, 360582922996807249, 360582923161522383, 360582923293103062, 360582923646292084, 360582923999790474]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 67070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 67000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594941139327118, 360594970051423933⟩, ⟨(-809372654422971261), (-808062394583662607)⟩, true⟩

def words08 : List Nat := [360582924295280170, 360582924518881157, 360582924604280674, 360582924689781519, 360582924719419410, 360582924861026575, 360582925166749464, 360582925472660992, 360582925596805517, 360582925777309914]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 67080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 67000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602582028932371, 360602610949966567⟩, ⟨(-1322088670511639827), (-1320777811020053569)⟩, true⟩

def words09 : List Nat := [360582926063049254, 360582926349056868, 360582926690554006, 360582926810526382, 360582926811424184, 360582926718513646, 360582926713384559, 360582926931891005, 360582927226012273, 360582927520345250]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 67090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 67000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 67000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk670B
