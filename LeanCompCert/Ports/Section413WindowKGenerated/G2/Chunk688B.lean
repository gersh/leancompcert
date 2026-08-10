import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk688A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk688B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk688A

def state06 : KState := ⟨⟨360532130564909607, 360532161085780205⟩, ⟨3484536204339844968, 3485955827182101024⟩, true⟩

def words05 : List Nat := [360582788383229186, 360582788277879272, 360582788172409548, 360582787939002084, 360582787537247974, 360582787053402419, 360582786569283432, 360582786206913064, 360582785633875495, 360582784899709658]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360570690480502900, 360570721010559841⟩, ⟨829093271972808926, 830513527433192434⟩, true⟩

def words06 : List Nat := [360582784165341515, 360582783493473831, 360582782955484458, 360582782628132112, 360582782300713654, 360582781793735646, 360582781293188041, 360582780864915595, 360582780436360090, 360582780158627697]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552578533981761, 360552609073329703⟩, ⟨2076517527522149422, 2077938422899131112⟩, true⟩

def words07 : List Nat := [360582779984403898, 360582779649743209, 360582779314919516, 360582778976239528, 360582778770263351, 360582778439895489, 360582778109439795, 360582777672571380, 360582777025027713, 360582776588180155]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360555405958418153, 360555436506938069⟩, ⟨1881811297014030936, 1883232824201945102⟩, true⟩

def words08 : List Nat := [360582776151002195, 360582775924358920, 360582775743007209, 360582775456459978, 360582775169760824, 360582774767752983, 360582774497454620, 360582774138975395, 360582773780400233, 360582773316695682]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603515385596237, 360603545943311213⟩, ⟨(-1432727229132437709), (-1431305068451590773)⟩, true⟩

def words09 : List Nat := [360582772920671061, 360582772735217533, 360582772549488966, 360582772396511197, 360582772352186342, 360582772128151412, 360582771903936471, 360582771981531460, 360582772283828234, 360582772586343222]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk688B
