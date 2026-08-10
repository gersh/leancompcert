import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk722A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk722B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk722A

def state06 : KState := ⟨⟨360611464728354725, 360611498466586071⟩, ⟨(-2107348255409985120), (-2105701568443182658)⟩, true⟩

def words05 : List Nat := [360582355682809193, 360582355765627855, 360582356039368749, 360582356396137684, 360582356589730216, 360582356783397102, 360582357061511747, 360582357436326793, 360582357840442025, 360582358244772878]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601117292504935, 360601151040532570⟩, ⟨(-1359754068949868793), (-1358106674057922147)⟩, true⟩

def words06 : List Nat := [360582358486619156, 360582358537368724, 360582358736573625, 360582358936073990, 360582359047073256, 360582359070187536, 360582359071108592, 360582358956475789, 360582358917106481, 360582359178318710]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360580461733533846, 360580495491212130⟩, ⟨133182948475871574, 134831040868781260⟩, true⟩

def words07 : List Nat := [360582359630305612, 360582360082476437, 360582360439128327, 360582360604769177, 360582360620027025, 360582360635542367, 360582360841864972, 360582360914045526, 360582360914969218, 360582360890228024]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588564520047044, 360588598287422118⟩, ⟨(-452496419651845786), (-450847626326297518)⟩, true⟩

def words08 : List Nat := [360582360869087921, 360582361020525694, 360582361230184059, 360582361440035191, 360582361478776566, 360582361479803066, 360582361492390810, 360582361594937391, 360582361633623302, 360582361720957050]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360577034973813620, 360577068750960332⟩, ⟨381004834680456653, 382654334445557597⟩, true⟩

def words09 : List Nat := [360582361721871523, 360582361713848755, 360582361705625971, 360582361778705133, 360582361779566016, 360582361774424670, 360582361769163241, 360582361645658015, 360582361414063645, 360582361342031502]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk722B
