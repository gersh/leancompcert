import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk803A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk803B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk803A

def state06 : KState := ⟨⟨360578354391543187, 360578396468151669⟩, ⟨301173295598414248, 303456923579902280⟩, true⟩

def words05 : List Nat := [360582173317715218, 360582173436320628, 360582173490600407, 360582173491749674, 360582173391546334, 360582173140108367, 360582172888456665, 360582172760568102, 360582172732493304, 360582172686712893]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592076071419506, 360592118158983493⟩, ⟨(-801672980684259210), (-799388472266490952)⟩, true⟩

def words06 : List Nat := [360582172640756103, 360582172516861953, 360582172320464878, 360582172279054806, 360582172237340409, 360582172157207253, 360582172128551710, 360582171969160879, 360582171809553899, 360582171928722995]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360573556061888498, 360573598160275821⟩, ⟨686966209046497496, 689251587390326722⟩, true⟩

def words07 : List Nat := [360582172181186603, 360582172433864232, 360582172599872698, 360582172770016894, 360582172898827103, 360582173027941181, 360582173180485649, 360582173181635370, 360582173179767558, 360582173074276696]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583973800628145, 360584015909883603⟩, ⟨(-150482509155801629), (-148196257178311303)⟩, true⟩

def words08 : List Nat := [360582172968544121, 360582172859209339, 360582172887186013, 360582172948431964, 360582172949494142, 360582172865482010, 360582172626767965, 360582172542981228, 360582172458817078, 360582172466498420]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565800559598435, 360565842679797767⟩, ⟨1310571791471675807, 1312858923282705205⟩, true⟩

def words09 : List Nat := [360582172467523199, 360582172404137788, 360582172340530863, 360582172395079986, 360582172396059307, 360582172356266699, 360582172316359430, 360582172198644636, 360582171972670377, 360582171770883373]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk803B
