import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk966A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk966B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk966A

def state06 : KState := ⟨⟨360597689665972412, 360597751421831721⟩, ⟨(-1495768748517668006), (-1491738007094286822)⟩, true⟩

def words05 : List Nat := [360582317005911164, 360582317195497535, 360582317431995357, 360582317728312178, 360582317965867712, 360582318203666047, 360582318345272895, 360582318422597996, 360582318583394436, 360582318744670361]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 96650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 96600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360610152437013726, 360610214206100487⟩, ⟨(-2700504966169064062), (-2696472946112647272)⟩, true⟩

def words06 : List Nat := [360582319012486401, 360582319244015091, 360582319393070524, 360582319542254717, 360582319663944569, 360582319839256229, 360582320121167137, 360582320403357399, 360582320618752432, 360582320908771271]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 96660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 96600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611720676029949, 360611782458346778⟩, ⟨(-2852068732337057266), (-2848035433264083210)⟩, true⟩

def words07 : List Nat := [360582321305448632, 360582321702533487, 360582322188218998, 360582322567508394, 360582322855029213, 360582323142651653, 360582323425722983, 360582323778753838, 360582324084601858, 360582324390750621]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 96670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 96600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602656090854920, 360602717886528077⟩, ⟨(-1975767409905304468), (-1971732819476781844)⟩, true⟩

def words08 : List Nat := [360582324608509459, 360582324719768405, 360582324918568271, 360582325117802951, 360582325274470260, 360582325373033684, 360582325417526269, 360582325462158160, 360582325571135838, 360582325783649042]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 96680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 96600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360591999052888004, 360592060861787709⟩, ⟨(-945315507766509749), (-941279638396609821)⟩, true⟩

def words09 : List Nat := [360582325959508595, 360582326135613154, 360582326252337634, 360582326337631976, 360582326383836961, 360582326430431845, 360582326583546711, 360582326739409036, 360582326841322069, 360582326943437366]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 96690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 96600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 96600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk966B
