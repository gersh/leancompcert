import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk480A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk480B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk480A

def state06 : KState := ⟨⟨360543850532108459, 360543864975466839⟩, ⟨1859442933187511995, 1859911994549302071⟩, true⟩

def words05 : List Nat := [360582566257981187, 360582566123526863, 360582566089011485, 360582566407980499, 360582566425705086, 360582566443527261, 360582566444116371, 360582566224357707, 360582565571774364, 360582564767280183]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360560753693455191, 360560768143050243⟩, ⟨1046918696535374281, 1047388057662534209⟩, true⟩

def words06 : List Nat := [360582563962595122, 360582563286016421, 360582562625042342, 360582561680841984, 360582560736573085, 360582559684190935, 360582558849630403, 360582558327208940, 360582557804752785, 360582556952238147]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360623900413419133, 360623914869253422⟩, ⟨(-1988910214669714606), (-1988440553591209220)⟩, true⟩

def words07 : List Nat := [360582556499510093, 360582556340938344, 360582556454320164, 360582556698453751, 360582556699064346, 360582556575675579, 360582556661555449, 360582557091174978, 360582557951896630, 360582558812732318]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581045933638669, 360581060395782014⟩, ⟨71559952583175373, 72029917032015293⟩, true⟩

def words08 : List Nat := [360582559336107986, 360582559635195827, 360582559924181915, 360582560213340631, 360582560293494563, 360582560294156344, 360582559942225038, 360582559302341157, 360582558662358372, 360582558210650636]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360531407671998670, 360531422140373394⟩, ⟨2459047724761258290, 2459517988908438372⟩, true⟩

def words09 : List Nat := [360582558579989615, 360582558980588543, 360582559003446930, 360582559004108929, 360582558706553076, 360582558301103571, 360582557895479488, 360582557480159983, 360582556632893852, 360582555570496231]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk480B
