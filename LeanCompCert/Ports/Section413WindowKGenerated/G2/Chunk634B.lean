import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk634A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk634B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk634A

def state06 : KState := ⟨⟨360554163860743684, 360554189614079302⟩, ⟨1808111100074802350, 1809215114901872866⟩, true⟩

def words05 : List Nat := [360582698700111702, 360582699284700993, 360582699715183777, 360582699898338145, 360582699899098100, 360582699882723645, 360582699866089877, 360582699855677632, 360582699597788451, 360582699149454371]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595404972738953, 360595430734506025⟩, ⟨(-809245356727827579), (-808140806798563693)⟩, true⟩

def words06 : List Nat := [360582698700932457, 360582698337037733, 360582698240759188, 360582698317154155, 360582698317976632, 360582698184228587, 360582698016363924, 360582698057059028, 360582698091276335, 360582698292811416]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593614760840576, 360593640531095815⟩, ⟨(-695562258869834270), (-694457170154122232)⟩, true⟩

def words07 : List Nat := [360582698369359291, 360582698446002075, 360582698770406558, 360582699250445861, 360582699665577909, 360582700080857028, 360582700370198239, 360582700578025923, 360582700751089155, 360582700924439428]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585662969448533, 360585688748111304⟩, ⟨(-190889112167183719), (-189783489697940967)⟩, true⟩

def words08 : List Nat := [360582701050405225, 360582701051297362, 360582700930115183, 360582700618970217, 360582700307689389, 360582699934086381, 360582699686006205, 360582699685951090, 360582699685798014, 360582699608080466]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360611147588713198, 360611173375797316⟩, ⟨(-1809049333130720349), (-1807943175950060173)⟩, true⟩

def words09 : List Nat := [360582699855872210, 360582700103929635, 360582700599498891, 360582700932007614, 360582701032742121, 360582701133532993, 360582701178086428, 360582701379695213, 360582701828794584, 360582702278083106]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk634B
