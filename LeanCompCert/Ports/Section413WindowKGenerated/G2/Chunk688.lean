import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk688

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360565027487324011, 360565057952909250⟩, ⟨1218705397845494491, 1220121215398078613⟩, true⟩

def state01 : KState := ⟨⟨360575438327663938, 360575468802442493⟩, ⟨502398566242560203, 503815016341048107⟩, true⟩

def words00 : List Nat := [360582792015924817, 360582791943250320, 360582791956046330, 360582791969014635, 360582791969926641, 360582791775023368, 360582791368973766, 360582791125585779, 360582790881922942, 360582790630902616]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582602032262560, 360582632516306509⟩, ⟨9419465537520080, 10836553233634472⟩, true⟩

def words01 : List Nat := [360582790525364842, 360582790314393832, 360582790103242681, 360582790207398507, 360582790259471579, 360582790311712372, 360582790312595516, 360582790191983991, 360582789979750300, 360582789978573781]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587897854160467, 360587928347365142⟩, ⟨(-355036383804201378), (-353618665619260928)⟩, true⟩

def words02 : List Nat := [360582790185505308, 360582790334649564, 360582790376840644, 360582790419144637, 360582790419960352, 360582790502980354, 360582790630521276, 360582790758239540, 360582790780388891, 360582790856036827]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589434462555527, 360589464964966977⟩, ⟨(-460865988489335343), (-459447636556592921)⟩, true⟩

def words03 : List Nat := [360582790927238897, 360582790998720693, 360582791141837938, 360582791142811500, 360582791128443805, 360582790930764259, 360582790732905826, 360582790728556708, 360582790826298434, 360582790924256404]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360566713949667649, 360566744461358739⟩, ⟨1103221019660185811, 1104640010446868845⟩, true⟩

def words04 : List Nat := [360582790925132095, 360582790917184783, 360582790698347082, 360582790615151703, 360582790531715340, 360582790306159906, 360582789968635308, 360582789509706708, 360582789050605762, 360582788615468353]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk688
