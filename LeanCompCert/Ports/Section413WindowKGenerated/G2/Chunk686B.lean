import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk686A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk686B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk686A

def state06 : KState := ⟨⟨360573343633015312, 360573373969788941⟩, ⟨647541557680997722, 648948522021504160⟩, true⟩

def words05 : List Nat := [360582828892678830, 360582828628068222, 360582828363174418, 360582828160873942, 360582827746594793, 360582827140578725, 360582826534377664, 360582826079290693, 360582825730709149, 360582825594053746]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360573318085476583, 360573348431521898⟩, ⟨649135831627199492, 650543432605824914⟩, true⟩

def words06 : List Nat := [360582825457271236, 360582825213217114, 360582824937920449, 360582824568745023, 360582824199323884, 360582823741988196, 360582823320113331, 360582822777891009, 360582822235498571, 360582821905129090]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360532429771532150, 360532460126718975⟩, ⟨3457199266251861799, 3458607495023406075⟩, true⟩

def words07 : List Nat := [360582821767960023, 360582821766550653, 360582821765039916, 360582821601720017, 360582821226458405, 360582820734192396, 360582820241669349, 360582819744895325, 360582819150959153, 360582818418725723]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573924278943369, 360573954643292380⟩, ⟨607163085185344264, 608571943261623308⟩, true⟩

def words08 : List Nat := [360582817686290831, 360582817126093726, 360582816672313441, 360582816430317591, 360582816188231709, 360582815770317212, 360582815209917731, 360582814861370356, 360582814512536987, 360582814330921753]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576529211944494, 360576559585555999⟩, ⟨428161117517720282, 429570611880311968⟩, true⟩

def words09 : List Nat := [360582814202823372, 360582813910002984, 360582813617000661, 360582813481348968, 360582813457917733, 360582813296305849, 360582813134602476, 360582812824509054, 360582812522799305, 360582812432890502]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk686B
