import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk196A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk196B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk196A

def state06 : KState := ⟨⟨360498863387242962, 360498865627314075⟩, ⟨1662384065566226823, 1662413870901692929⟩, true⟩

def words05 : List Nat := [360583429511116670, 360583432073992976, 360583433340408710, 360583433340660482, 360583433175545674, 360583432359700383, 360583431543857408, 360583431118030574, 360583428110949250, 360583423809964212]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360529387356756806, 360529389599206811⟩, ⟨1062271756474010289, 1062301608589976107⟩, true⟩

def words06 : List Nat := [360583419509360044, 360583417781354289, 360583417612516580, 360583416980832678, 360583416349196180, 360583413391281861, 360583407853545667, 360583404061623457, 360583400270013172, 360583395781646566]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360464366597680225, 360464368842525027⟩, ⟨2341735259910929101, 2341765159144836771⟩, true⟩

def words07 : List Nat := [360583393036398774, 360583388811629966, 360583384587242641, 360583382156013780, 360583381013420233, 360583379167241121, 360583377321225985, 360583373459839886, 360583367020963895, 360583360974595395]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360546531180803715, 360546533428021482⟩, ⟨724232023494933476, 724261969440561016⟩, true⟩

def words08 : List Nat := [360583354928758301, 360583351450544859, 360583347281925401, 360583341823237833, 360583336365059136, 360583329704362681, 360583324842910300, 360583322547868013, 360583320253030999, 360583316666692918]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360627111003327985, 360627113252927304⟩, ⟨(-863273089372417040), (-863243096522416766)⟩, true⟩

def words09 : List Nat := [360583314798877639, 360583311792976061, 360583308787303857, 360583307416889058, 360583304630410846, 360583299538700521, 360583294447459087, 360583291919954628, 360583293806142089, 360583296030627806]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk196B
