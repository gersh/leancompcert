import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk720A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk720B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk720A

def state06 : KState := ⟨⟨360586918095183215, 360586951639605180⟩, ⟨(-333808704853546874), (-332176003171563634)⟩, true⟩

def words05 : List Nat := [360582341059943961, 360582341003219659, 360582341080873241, 360582341313189153, 360582341496311986, 360582341679596460, 360582341766752382, 360582341859463993, 360582341924267504, 360582341989403663]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566392634102950, 360566426188148276⟩, ⟨1145305782285087422, 1146939177475339632⟩, true⟩

def words06 : List Nat := [360582342083847276, 360582342084870124, 360582342034883808, 360582341844102294, 360582341653175233, 360582341298703103, 360582341040835291, 360582340868153303, 360582340695364327, 360582340426770107]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586854795252154, 360586888358973640⟩, ⟨(-329501669852968655), (-327867577256659025)⟩, true⟩

def words07 : List Nat := [360582340206783984, 360582340127784141, 360582340160464360, 360582340161487362, 360582340082285841, 360582339844155217, 360582339605834873, 360582339631681486, 360582339695629988, 360582339759796927]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592107489873922, 360592141063345118⟩, ⟨(-708292291181101770), (-706657495777780796)⟩, true⟩

def words08 : List Nat := [360582339760717057, 360582339727872855, 360582339606394972, 360582339514905615, 360582339423151874, 360582339227843492, 360582339101943023, 360582338880248598, 360582338658364475, 360582338764919826]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594058528842657, 360594092111964864⟩, ⟨(-848902657557929861), (-847267166365400159)⟩, true⟩

def words09 : List Nat := [360582339093819475, 360582339422906055, 360582339601926149, 360582339823605136, 360582339996278750, 360582340169218697, 360582340407763597, 360582340668664497, 360582340832572936, 360582340996635460]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk720B
