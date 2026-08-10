import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk891A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk891B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk891A

def state06 : KState := ⟨⟨360571086243746462, 360571138459280779⟩, ⟨970992436238194312, 974136268630689616⟩, true⟩

def words05 : List Nat := [360582063935587906, 360582063906235933, 360582063971594804, 360582064151535485, 360582064250407897, 360582064349481610, 360582064381936894, 360582064383222374, 360582064289963785, 360582064168888571]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 89150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 89100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360568132383482323, 360568184611122383⟩, ⟨1234356508842767768, 1237501420643874970⟩, true⟩

def words06 : List Nat := [360582064047388603, 360582064024773319, 360582063902611533, 360582063718146403, 360582063533478579, 360582063275536617, 360582063133776368, 360582062981212026, 360582062828510908, 360582062612923930]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 89160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 89100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566839549641624, 360566891789434661⟩, ⟨1349597929768113069, 1352743925308420209⟩, true⟩

def words07 : List Nat := [360582062458331064, 360582062363435902, 360582062268169928, 360582062170227114, 360582061946607977, 360582061605684777, 360582061264529809, 360582060920973882, 360582060649860617, 360582060481129082]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 89170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 89100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574924052096551, 360574976304139636⟩, ⟨628506771835513162, 631653859895365960⟩, true⟩

def words08 : List Nat := [360582060312197728, 360582060077485049, 360582059855484398, 360582059728380969, 360582059600939193, 360582059442028850, 360582059228482493, 360582058916961067, 360582058605191366, 360582058419398022]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 89180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 89100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360568324887446611, 360568377151596936⟩, ⟨1217188604804910328, 1220336772770087396⟩, true⟩

def words09 : List Nat := [360582058357524413, 360582058375300814, 360582058376452007, 360582058314596281, 360582058295362385, 360582058244807112, 360582058247134669, 360582058248420861, 360582058209163366, 360582058057121265]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 89190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 89100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 89100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk891B
