import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk760A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk760B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk760A

def state06 : KState := ⟨⟨360569749277506668, 360569786809396680⟩, ⟨941593575844991643, 943521666231736659⟩, true⟩

def words05 : List Nat := [360582191871111215, 360582192060929679, 360582192147146395, 360582192208481170, 360582192209404735, 360582192117572746, 360582192025427136, 360582192009535654, 360582191936743828, 360582191774769172]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 76050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 76000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571297375569893, 360571334917705416⟩, ⟨823891776452981961, 825820646164870913⟩, true⟩

def words06 : List Nat := [360582191612554469, 360582191580156968, 360582191682343944, 360582191784731604, 360582191785738155, 360582191718897757, 360582191527358576, 360582191346317566, 360582191164967457, 360582190979834572]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 76060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 76000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566717229625203, 360566754782085504⟩, ⟨1172328988583063760, 1174258643750736146⟩, true⟩

def words07 : List Nat := [360582190838090962, 360582190610021258, 360582190381749492, 360582190290364936, 360582190291275942, 360582190188173765, 360582190084931415, 360582189883029359, 360582189508483942, 360582189306845635]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 76070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 76000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565803855654192, 360565841418338465⟩, ⟨1241801536625828329, 1243731969685409221⟩, true⟩

def words08 : List Nat := [360582189104852616, 360582189075605242, 360582188912940346, 360582188617389519, 360582188321668226, 360582187982716985, 360582187733266772, 360582187510927302, 360582187288480183, 360582186956118534]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 76080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 76000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586414806885463, 360586452379799792⟩, ⟨(-326613446060601331), (-324682234546148405)⟩, true⟩

def words09 : List Nat := [360582186742179643, 360582186701057821, 360582186736458652, 360582186737543048, 360582186643020157, 360582186403076276, 360582186162945256, 360582185917303376, 360582185857854035, 360582185915041824]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 76090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 76000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 76000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk760B
