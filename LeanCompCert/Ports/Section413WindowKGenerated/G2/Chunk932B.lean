import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk932A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk932B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk932A

def state06 : KState := ⟨⟨360609094115968370, 360609151444324514⟩, ⟨(-2531948391501488758), (-2528338133511126264)⟩, true⟩

def words05 : List Nat := [360582040117334937, 360582040087731560, 360582040141575752, 360582040229636768, 360582040230881580, 360582040221252086, 360582040315318677, 360582040512772755, 360582040804566524, 360582041096660313]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598770677579797, 360598828018807994⟩, ⟨(-1569155621510393171), (-1565544163009073881)⟩, true⟩

def words06 : List Nat := [360582041300109227, 360582041528492799, 360582041871522865, 360582042214943607, 360582042496413047, 360582042663445421, 360582042760231453, 360582042857174518, 360582042939933193, 360582043121433579]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566723587306319, 360566780941246594⟩, ⟨1420088835547216185, 1423701479767135689⟩, true⟩

def words07 : List Nat := [360582043352641506, 360582043584101068, 360582043757648944, 360582043843599884, 360582043844756744, 360582043821492187, 360582043839648726, 360582043840998811, 360582043769412295, 360582043607196071]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592357738379137, 360592415105074867⟩, ⟨(-971140202852060591), (-967526368739902981)⟩, true⟩

def words08 : List Nat := [360582043444667169, 360582043437891385, 360582043594306599, 360582043750977288, 360582043810984378, 360582043812334611, 360582043816563431, 360582043877060950, 360582043934537539, 360582044047108505]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582974367106601, 360583031746654730⟩, ⟨(-95722685995129322), (-92107652820280530)⟩, true⟩

def words09 : List Nat := [360582044069803971, 360582044092638264, 360582044177145959, 360582044331232727, 360582044439213948, 360582044547440540, 360582044587518559, 360582044588868957, 360582044524824890, 360582044536948293]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk932B
