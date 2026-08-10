import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk751A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk751B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk751A

def state06 : KState := ⟨⟨360526730339900050, 360526766954425719⟩, ⟨4170645803195537901, 4172504530864861773⟩, true⟩

def words05 : List Nat := [360582285783271951, 360582285595399147, 360582285407393974, 360582285087426969, 360582284647759442, 360582284163641079, 360582283679224100, 360582283255013006, 360582282653777815, 360582281916252022]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574569225909459, 360574605850538786⟩, ⟨574808613748014335, 576668100857875877⟩, true⟩

def words06 : List Nat := [360582281178503455, 360582280617862875, 360582280146043644, 360582279701871372, 360582279257623723, 360582278662831337, 360582278162659591, 360582277839577899, 360582277516177641, 360582277369773293]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360557489442392158, 360557526077230034⟩, ⟨1858803708998648514, 1860663963535133344⟩, true⟩

def words07 : List Nat := [360582277268672831, 360582277079172428, 360582276889487354, 360582276696088514, 360582276673135987, 360582276558581836, 360582276443923129, 360582276240154700, 360582275859352050, 360582275531387192]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360540934137674173, 360540970782583011⟩, ⟨3103515408119463426, 3105376419842249222⟩, true⟩

def words08 : List Nat := [360582275203054462, 360582275051616483, 360582274723238549, 360582274287642591, 360582273851889308, 360582273300425657, 360582272836880418, 360582272317784040, 360582271798585095, 360582271173856349]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360577007947906717, 360577044602922692⟩, ⟨390914545782321421, 392776317510497865⟩, true⟩

def words09 : List Nat := [360582270625451364, 360582270137375848, 360582269648993692, 360582269337487936, 360582269087982764, 360582268683625550, 360582268279067724, 360582267970027393, 360582267760598158, 360582267692251290]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk751B
