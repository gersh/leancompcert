import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk902A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk902B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk902A

def state06 : KState := ⟨⟨362491909018246151, 362492032322520102⟩, ⟨(-631542464854600628), (-624028050250601410)⟩, true⟩

def words05 : List Nat := [371285118313240159, 371285118400878004, 371285118564608449, 371285118567758083, 371285118568175584, 371285118529437998, 371285118548719120, 371285118568093903, 371285118646838848, 371285118726944487]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484482676995751, 362484606009677345⟩, ⟨38760630274755376, 46277609099062602⟩, true⟩

def words06 : List Nat := [371285118804607031, 371285118807756902, 371285118755975041, 371285118794163897, 371285118836250184, 371285118839421740, 371285118773472165, 371285118708390535, 371285118663722615, 371285118667360951]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362468426788999577, 362468550150110416⟩, ⟨1488279257009718319, 1495798802283559383⟩, true⟩

def words07 : List Nat := [371285118780816216, 371285118901354895, 371285119020544690, 371285119023694748, 371285118979196381, 371285118948630585, 371285118922473327, 371285118925623516, 371285118770497375, 371285118590543331]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484139720134005, 362484263109465416⟩, ⟨69673505100429347, 77195598264975597⟩, true⟩

def words08 : List Nat := [371285118409158690, 371285118351765094, 371285118237820461, 371285118237471986, 371285118236182828, 371285118226111735, 371285118113038282, 371285118063079974, 371285118080157200, 371285118083418955]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483865395732534, 362483988813758649⟩, ⟨94447479560725323, 101972163713664767⟩, true⟩

def words09 : List Nat := [371285118076304903, 371285118070088706, 371285118103912767, 371285118107385716, 371285118110437642, 371285118133050089, 371285118151892175, 371285118155062972, 371285118082163920, 371285118073600440]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk902B
