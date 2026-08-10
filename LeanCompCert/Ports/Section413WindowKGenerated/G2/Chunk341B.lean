import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk341A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk341B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk341A

def state06 : KState := ⟨⟨360568657053243481, 360568664148712204⟩, ⟨438274953693474421, 438438829330738715⟩, true⟩

def words05 : List Nat := [360581510196015571, 360581509956113442, 360581509716099379, 360581508941963448, 360581507313994284, 360581504795763743, 360581502277593306, 360581500615756142, 360581499384313024, 360581499009055610]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 34150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 34100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590996368213750, 360591003468037390⟩, ⟨(-325140790528978767), (-324976766106965383)⟩, true⟩

def words06 : List Nat := [360581498633746292, 360581497735039656, 360581496944548899, 360581496787527437, 360581496630387360, 360581496256031065, 360581495758362941, 360581494610242021, 360581493462101034, 360581493159117342]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 34160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 34100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560514577640495, 360560521681768929⟩, ⟨716781335131715244, 716945506670993468⟩, true⟩

def words07 : List Nat := [360581494293174880, 360581495427253527, 360581496133423729, 360581496861805499, 360581497361101726, 360581497860489232, 360581498061848092, 360581498062306280, 360581497880326164, 360581497267101609]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 34170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 34100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588103859872953, 360588110968329234⟩, ⟨(-226459338775321169), (-226295019289798241)⟩, true⟩

def words08 : List Nat := [360581496653816768, 360581495730727368, 360581495638606030, 360581496020247695, 360581496020669828, 360581495644210229, 360581494415652630, 360581493465821249, 360581492515899382, 360581492413174668]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 34180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 34100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360545436383341948, 360545443496157673⟩, ⟨1232632212236588278, 1232796680792737964⟩, true⟩

def words09 : List Nat := [360581492413586604, 360581492051792318, 360581491839074652, 360581492532339007, 360581492636342223, 360581492740407509, 360581492740815406, 360581492414398360, 360581491236229804, 360581490182730561]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 34190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 34100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 34100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk341B
