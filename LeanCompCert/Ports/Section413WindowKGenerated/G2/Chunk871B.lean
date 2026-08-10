import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk871A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk871B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk871A

def state06 : KState := ⟨⟨360565470248509155, 360565520060193231⟩, ⟨1448494294476846622, 1451426193697135172⟩, true⟩

def words05 : List Nat := [360582172100094059, 360582172407731658, 360582172608352114, 360582172677550381, 360582172713438591, 360582172749673115, 360582172782175969, 360582172783430589, 360582172684483172, 360582172494723947]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 87150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 87100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593006214492625, 360593056038015260⟩, ⟨(-951687434970830645), (-948754503844110851)⟩, true⟩

def words06 : List Nat := [360582172304684778, 360582172198985782, 360582172222796877, 360582172285004786, 360582172286178439, 360582172232164774, 360582172100658367, 360582172063801344, 360582172080033818, 360582172206192245]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 87160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 87100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360603653401819966, 360603703237314274⟩, ⟨(-1879915447006678095), (-1876981472251494045)⟩, true⟩

def words07 : List Nat := [360582172227535930, 360582172249000573, 360582172380022932, 360582172596007374, 360582172724566536, 360582172853322551, 360582172916105852, 360582173032959032, 360582173280935962, 360582173529324558]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 87170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 87100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360606097499047257, 360606147346343692⟩, ⟨(-2093028646790369075), (-2090093643064852449)⟩, true⟩

def words08 : List Nat := [360582173908682098, 360582174156791170, 360582174337877143, 360582174519084398, 360582174596582512, 360582174773612962, 360582175081636091, 360582175389892955, 360582175632198152, 360582175908430779]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 87180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 87100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588753879418565, 360588803738581981⟩, ⟨(-580793954202847499), (-577857915735999397)⟩, true⟩

def words09 : List Nat := [360582176166084265, 360582176424130818, 360582176661113410, 360582176766877641, 360582176768035237, 360582176761920290, 360582176768602943, 360582176849291858, 360582176926320617, 360582177003616373]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 87190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 87100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 87100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk871B
