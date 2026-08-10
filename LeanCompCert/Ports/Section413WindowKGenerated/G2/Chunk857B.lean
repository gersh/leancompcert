import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk857A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk857B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk857A

def state06 : KState := ⟨⟨360573555352252434, 360573603516305387⟩, ⟨745620241674212020, 748409683498032704⟩, true⟩

def words05 : List Nat := [360582331978497903, 360582331833654433, 360582331688439118, 360582331617984339, 360582331456282338, 360582331179162603, 360582330901822034, 360582330621198671, 360582330408807005, 360582330308323788]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 85750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 85700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360570798706153432, 360570846881958252⟩, ⟨981934183882428251, 984724633602985807⟩, true⟩

def words06 : List Nat := [360582330207680328, 360582330020596616, 360582329729254647, 360582329548541031, 360582329367483816, 360582329105926314, 360582328852581182, 360582328487775697, 360582328122742165, 360582327873372535]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 85760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 85700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360563308659416898, 360563356846844648⟩, ⟨1624367129532150444, 1627158576210107862⟩, true⟩

def words07 : List Nat := [360582327740530077, 360582327604307491, 360582327467952961, 360582327263593600, 360582327020483269, 360582326715844397, 360582326410851185, 360582326189188344, 360582326040548478, 360582325820687154]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 85770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 85700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586984865141217, 360587033064207752⟩, ⟨(-406640680757492046), (-403848235648094306)⟩, true⟩

def words08 : List Nat := [360582325600551112, 360582325538240538, 360582325671512897, 360582325805018557, 360582325819309705, 360582325820543155, 360582325745435220, 360582325711155767, 360582325676508919, 360582325714536481]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 85780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 85700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572869912468406, 360572918123294608⟩, ⟨804427289761739439, 807220743790161707⟩, true⟩

def words09 : List Nat := [360582325715635088, 360582325703646775, 360582325813885551, 360582326012468992, 360582326176511448, 360582326340751540, 360582326437104868, 360582326438338204, 360582326398700287, 360582326290471650]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 85790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 85700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 85700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk857B
