import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk832

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578339455780742, 360578384680987999⟩, ⟨335029647978704581, 337570795953313029⟩, true⟩

def state01 : KState := ⟨⟨360593769404612123, 360593814641095128⟩, ⟨(-948805869991107215), (-946263783818914209)⟩, true⟩

def words00 : List Nat := [360582441974487649, 360582441986301068, 360582442191302402, 360582442396536721, 360582442475438791, 360582442476632202, 360582442489351077, 360582442568714455, 360582442643899507, 360582442781799856]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578049329782986, 360578094577633810⟩, ⟨359321622557889974, 361864654700765774⟩, true⟩

def words01 : List Nat := [360582442847059011, 360582442912446951, 360582442965893306, 360582443121768186, 360582443142722708, 360582443163882698, 360582443164946191, 360582443113639848, 360582442918050357, 360582442867163981]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593631788320488, 360593677047428278⟩, ⟨(-937602687653325051), (-935058718650814097)⟩, true⟩

def words02 : List Nat := [360582442907925522, 360582442909119208, 360582442858206873, 360582442696342844, 360582442534289031, 360582442334630255, 360582442336037933, 360582442409591025, 360582442410654589, 360582442546837744]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590786196902831, 360590831467276346⟩, ⟨(-700683216998578212), (-698138310293124608)⟩, true⟩

def words03 : List Nat := [360582442827045689, 360582443107613497, 360582443532069344, 360582443812738748, 360582443974262008, 360582444135873413, 360582444187215277, 360582444311086479, 360582444412817135, 360582444514809496]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577610973443953, 360577656255196313⟩, ⟨396016505628608893, 398562359563471115⟩, true⟩

def words04 : List Nat := [360582444544134076, 360582444545328155, 360582444459064603, 360582444488903967, 360582444489903252, 360582444483326456, 360582444364612042, 360582444173668701, 360582443982495485, 360582443791046926]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk832
