import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk886A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk886B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk886A

def state06 : KState := ⟨⟨360552905528673073, 360552957137661424⟩, ⟨2580963592564204898, 2584053496829614372⟩, true⟩

def words05 : List Nat := [360582104559836518, 360582104512070725, 360582104464167039, 360582104337936164, 360582104156812567, 360582103856145545, 360582103555109928, 360582103381332524, 360582103116953955, 360582102789554382]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577711625603974, 360577763246658188⟩, ⟨381605011055738411, 384695985141565521⟩, true⟩

def words06 : List Nat := [360582102461855921, 360582102261562594, 360582102182643286, 360582102207443141, 360582102208623492, 360582102113302545, 360582101937407124, 360582101888890310, 360582101840002952, 360582101760080333]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360563164859862858, 360563216493084936⟩, ⟨1671513165292664095, 1674605218363904495⟩, true⟩

def words07 : List Nat := [360582101712298544, 360582101568184347, 360582101423832157, 360582101262732914, 360582101165109081, 360582101035043429, 360582100904830043, 360582100693868892, 360582100389938147, 360582100178452143]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360578949839622491, 360579001484905670⟩, ⟨271627387901200462, 274720510609064160⟩, true⟩

def words08 : List Nat := [360582099966545861, 360582099881850775, 360582099826729093, 360582099658740685, 360582099490547502, 360582099290761724, 360582099172606698, 360582099157915419, 360582099143087378, 360582099021387901]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578755669149468, 360578807326492446⟩, ⟨288841171327335047, 291935363678319741⟩, true⟩

def words09 : List Nat := [360582099030561412, 360582099075036821, 360582099135615288, 360582099136893999, 360582099109800362, 360582098975199137, 360582098840373991, 360582098703028472, 360582098629056645, 360582098593275742]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk886B
