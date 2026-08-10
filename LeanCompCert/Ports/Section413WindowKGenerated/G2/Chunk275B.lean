import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk275A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk275B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk275A

def state06 : KState := ⟨⟨360578563248685596, 360578567783817019⟩, ⟨117340529316784767, 117425069278768497⟩, true⟩

def words05 : List Nat := [360582829017891260, 360582829142500225, 360582830138539578, 360582830575004831, 360582830575341399, 360582829702462888, 360582828829579199, 360582828644176587, 360582828644475358, 360582828490249486]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575202941273384, 360575207479857128⟩, ⟨209631012139969164, 209715647265536052⟩, true⟩

def words06 : List Nat := [360582828335980913, 360582827520889862, 360582825394765937, 360582824080024383, 360582822765282604, 360582820756483126, 360582819464221507, 360582817504645845, 360582815545143651, 360582814140983916]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360481075694162199, 360481080236170683⟩, ⟨2805435594395848623, 2805520323958682193⟩, true⟩

def words07 : List Nat := [360582814512028650, 360582815158989441, 360582815159319997, 360582814686886858, 360582813805604340, 360582812585913389, 360582811366203574, 360582809799771322, 360582806923629170, 360582803235589055]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360568990116403134, 360568994661838185⟩, ⟨380420723079028145, 380505547163583393⟩, true⟩

def words08 : List Nat := [360582799547728053, 360582797170378525, 360582795454922084, 360582795049702675, 360582794644487334, 360582793109791316, 360582791206452335, 360582789219372148, 360582787232326504, 360582786091601273]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360516128286069876, 360516132834965397⟩, ⟨1839305384081988167, 1839390303657837013⟩, true⟩

def words09 : List Nat := [360582785592073367, 360582784149974588, 360582782707911071, 360582782382879584, 360582782399825515, 360582782416829462, 360582782417153269, 360582781775299099, 360582779825515842, 360582777411184884]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk275B
