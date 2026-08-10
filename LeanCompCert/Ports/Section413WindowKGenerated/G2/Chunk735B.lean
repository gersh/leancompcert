import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk735A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk735B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk735A

def state06 : KState := ⟨⟨360570840968604152, 360570875981318229⟩, ⟨848426676138085312, 850166288214453496⟩, true⟩

def words05 : List Nat := [360582433732693681, 360582433579037487, 360582433455026567, 360582433634745229, 360582433739197337, 360582433843835642, 360582433844782389, 360582433810181790, 360582433590862728, 360582433434937241]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360572167952136881, 360572202974713718⟩, ⟨750766853150942841, 752507190781017625⟩, true⟩

def words06 : List Nat := [360582433306057893, 360582433307103506, 360582433150929054, 360582432858446678, 360582432565801631, 360582432226683940, 360582432011411652, 360582431850984210, 360582431690438006, 360582431426403008]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360565818950293454, 360565853982739394⟩, ⟨1217915380303382213, 1219656444052346699⟩, true⟩

def words07 : List Nat := [360582431333641070, 360582431380213024, 360582431431272566, 360582431432318446, 360582431299036809, 360582431014107290, 360582430728998528, 360582430383287780, 360582430130335972, 360582429906143205]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360561347685713797, 360561382728116293⟩, ⟨1546797650098854692, 1548539446501067978⟩, true⟩

def words08 : List Nat := [360582429681800770, 360582429365521250, 360582428864619012, 360582428548459007, 360582428231999434, 360582427868992655, 360582427321462755, 360582426661291832, 360582426000938669, 360582425525323809]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360542194929662122, 360542229981924638⟩, ⟨2956309906960581993, 2958052429011407973⟩, true⟩

def words09 : List Nat := [360582425240241914, 360582424951374341, 360582424662416954, 360582424216655373, 360582423661127033, 360582423016019517, 360582422370622607, 360582421909791637, 360582421456660663, 360582420911666641]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk735B
