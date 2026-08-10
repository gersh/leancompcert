import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk347A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk347B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk347A

def state06 : KState := ⟨⟨360668268471295793, 360668275828773191⟩, ⟨(-3005857989390850266), (-3005685084717584666)⟩, true⟩

def words05 : List Nat := [360581795054950989, 360581796711874696, 360581798747525215, 360581799958776198, 360581800372687974, 360581800786605183, 360581802027519897, 360581803688761245, 360581806176828876, 360581808664861981]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 34750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 34700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360659287009570241, 360659294371485419⟩, ⟨(-2693641201054450626), (-2693468142101978468)⟩, true⟩

def words06 : List Nat := [360581810735344824, 360581813185839470, 360581816462978256, 360581819740064925, 360581822520246810, 360581824476369641, 360581826019355488, 360581827562300048, 360581829080700121, 360581831309102917]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 34760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 34700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360568262400905357, 360568269767208478⟩, ⟨471752356157336033, 471925567700031715⟩, true⟩

def words07 : List Nat := [360581833355490552, 360581835401846919, 360581836944792303, 360581837664065218, 360581837909958938, 360581838155974426, 360581839006834028, 360581839034193587, 360581839034608674, 360581838644945685]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 34770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 34700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360619837320100350, 360619844690809741⟩, ⟨(-1322255907057047161), (-1322082542243184341)⟩, true⟩

def words08 : List Nat := [360581838691164762, 360581839855618895, 360581840995813939, 360581842136026261, 360581842569795834, 360581842570262037, 360581842299043670, 360581842417843050, 360581842892611335, 360581843985390432]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 34780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 34700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569624019485650, 360569631394630641⟩, ⟨425005373394009882, 425178892544666636⟩, true⟩

def words09 : List Nat := [360581844661576551, 360581845337774886, 360581846131581466, 360581847344360602, 360581848348197903, 360581849352053735, 360581849724870293, 360581849725336688, 360581849529462480, 360581849178899166]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 34790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 34700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 34700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk347B
