import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk633A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk633B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk633A

def state06 : KState := ⟨⟨360562790397776829, 360562816066826327⟩, ⟨1258163548288586516, 1259262218536872168⟩, true⟩

def words05 : List Nat := [360582692463672378, 360582692131410284, 360582691798988251, 360582691755721257, 360582691756466322, 360582691734648615, 360582691712748227, 360582691496134251, 360582691098837228, 360582690786184548]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574733504063285, 360574759181490497⟩, ⟨501392328326929477, 502491529429286809⟩, true⟩

def words06 : List Nat := [360582690473230057, 360582690409235942, 360582690271382651, 360582690008412411, 360582689745292362, 360582689283490199, 360582688974445148, 360582688914305314, 360582688854078289, 360582688667515893]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588648598877202, 360588674284722269⟩, ⟨(-380613960522763360), (-379514225939551360)⟩, true⟩

def words07 : List Nat := [360582688543125381, 360582688287654094, 360582688031929761, 360582687972484225, 360582687664980670, 360582687144549713, 360582686623962272, 360582686352331490, 360582686366067137, 360582686461463887]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596485638898260, 360596511333220758⟩, ⟨(-877474855681073979), (-876374583756850075)⟩, true⟩

def words08 : List Nat := [360582686462257744, 360582686394105444, 360582686584400186, 360582686780466974, 360582686805800213, 360582686806691320, 360582686687958024, 360582686445676017, 360582686208624673, 360582686427733278]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571089025232962, 360571114727954734⟩, ⟨732633475903050348, 733734280299670538⟩, true⟩

def words09 : List Nat := [360582686895094002, 360582687362626072, 360582687608968330, 360582687722219170, 360582687730439296, 360582687738904666, 360582687995615136, 360582688004671495, 360582688005479052, 360582687823858515]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk633B
