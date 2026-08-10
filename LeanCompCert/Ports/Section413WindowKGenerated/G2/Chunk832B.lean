import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk832A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk832B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk832A

def state06 : KState := ⟨⟨360562529328287144, 360562574621298980⟩, ⟨1651615880062631278, 1654162671405931622⟩, true⟩

def words05 : List Nat := [360582443734522180, 360582443674439780, 360582443614222923, 360582443481785572, 360582443205218913, 360582442892732526, 360582442579902981, 360582442411508889, 360582442294082989, 360582442056699004]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608415817509185, 360608461121794350⟩, ⟨(-2169163313869544610), (-2166615583854341668)⟩, true⟩

def words06 : List Nat := [360582441819048126, 360582441696633297, 360582441694493927, 360582441744157775, 360582441745284091, 360582441662261829, 360582441665820144, 360582441740515383, 360582441958980325, 360582442272688968]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604889354364737, 360604934670030631⟩, ⟨(-1875471302256013704), (-1872922624509581698)⟩, true⟩

def words07 : List Nat := [360582442497853529, 360582442723163383, 360582443092346212, 360582443533990369, 360582443937470212, 360582444341134191, 360582444657786716, 360582444932883929, 360582445203916204, 360582445475322240]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591463294926849, 360591508621840466⟩, ⟨(-757358560636285859), (-754808946122745413)⟩, true⟩

def words08 : List Nat := [360582445731031045, 360582445843107601, 360582445844176676, 360582445833327605, 360582445822283530, 360582445836474918, 360582445981900843, 360582446127552779, 360582446200791750, 360582446310833002]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360591037352574549, 360591082690787973⟩, ⟨(-721981084211928675), (-719430528483558305)⟩, true⟩

def words09 : List Nat := [360582446413972875, 360582446517465090, 360582446585961551, 360582446587156556, 360582446511973825, 360582446313759948, 360582446115320053, 360582446004237652, 360582446068533898, 360582446173477454]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk832B
