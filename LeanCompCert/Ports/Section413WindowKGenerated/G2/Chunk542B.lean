import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk542A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk542B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk542A

def state06 : KState := ⟨⟨360561806406023927, 360561824999144813⟩, ⟨1084777871040906070, 1085459514529924222⟩, true⟩

def words05 : List Nat := [360581833371046496, 360581833137690396, 360581832931791518, 360581832932545073, 360581832621776505, 360581832021762540, 360581831421637938, 360581830700460735, 360581830149851684, 360581829781941163]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360559642343102827, 360559660943408836⟩, ⟨1202037008516170571, 1202719041904783937⟩, true⟩

def words06 : List Nat := [360581829413941809, 360581828875153657, 360581828239016996, 360581827654121947, 360581827069030549, 360581826398568324, 360581825518679184, 360581824469327546, 360581823419870309, 360581822709428825]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541065496933164, 360541084104345146⟩, ⟨2210281125112189353, 2210963544177952591⟩, true⟩

def words07 : List Nat := [360581822301695158, 360581821886258222, 360581821470754262, 360581820855288545, 360581820188308137, 360581819324012575, 360581818459527936, 360581817933861662, 360581817417445187, 360581816667797209]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563820690336798, 360563839304866559⟩, ⟨974928720326263727, 975611525779190743⟩, true⟩

def words08 : List Nat := [360581815918007070, 360581815142729170, 360581814548567023, 360581814105095782, 360581813661598924, 360581812871668841, 360581811742945905, 360581810953020440, 360581810162890705, 360581809677417291]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360561766319838549, 360561784941555730⟩, ⟨1086518199339812884, 1087201395034206872⟩, true⟩

def words09 : List Nat := [360581809347088245, 360581808847423432, 360581808347619387, 360581808195065534, 360581808195696795, 360581808119644145, 360581808043513790, 360581807794874169, 360581807434571807, 360581807066694482]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk542B
