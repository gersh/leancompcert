import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk856

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360534723033280227, 360534771010903480⟩, ⟨4070630504706987084, 4073403973243799156⟩, true⟩

def state01 : KState := ⟨⟨360567079424148885, 360567127413401871⟩, ⟨1300743961031153396, 1303518425130620812⟩, true⟩

def words00 : List Nat := [360582356951001926, 360582356532834947, 360582356217701833, 360582355899219582, 360582355580654567, 360582355145132512, 360582354646998916, 360582354285600681, 360582353923835181, 360582353653620662]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 85600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 85600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567547838137360, 360567595839104090⟩, ⟨1260587510003115950, 1263362976973348334⟩, true⟩

def words01 : List Nat := [360582353476863014, 360582353231755895, 360582352986422471, 360582352722370385, 360582352540477250, 360582352324444991, 360582352108314230, 360582351783441206, 360582351475782577, 360582351304847764]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 85610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 85600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575387139938219, 360575435152488893⟩, ⟨589352826038050153, 592129284883085621⟩, true⟩

def words02 : List Nat := [360582351133507758, 360582351098712877, 360582350983311359, 360582350799609445, 360582350615682291, 360582350386717423, 360582350247486841, 360582350244781392, 360582350241946431, 360582350127204333]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 85620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 85600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583499245098864, 360583547269280693⟩, ⟨(-105431547648293709), (-102654092769100673)⟩, true⟩

def words03 : List Nat := [360582350047468182, 360582349911657115, 360582349775489823, 360582349699599868, 360582349532893016, 360582349232205458, 360582348931289722, 360582348705336526, 360582348598076878, 360582348613347565]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 85630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 85600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585098419032706, 360585146454934541⟩, ⟨(-242500019747276830), (-239721561110234568)⟩, true⟩

def words04 : List Nat := [360582348614444096, 360582348561242941, 360582348371423808, 360582348318224873, 360582348264697854, 360582348118806964, 360582348021124087, 360582347855165126, 360582347688974082, 360582347636927627]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 85640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 85600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360547752309003415, 360547800356513304⟩, ⟨2956470205988180445, 2959249658912564963⟩, true⟩

def words05 : List Nat := [360582347770246694, 360582347903824945, 360582347959019331, 360582347960250478, 360582347908124778, 360582347792657972, 360582347676843135, 360582347515305591, 360582347217318730, 360582346815291177]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 85650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 85600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592844968763420, 360592893027894654⟩, ⟨(-906426504030023449), (-903646055563675059)⟩, true⟩

def words06 : List Nat := [360582346412993631, 360582346147260244, 360582345949573538, 360582345798396764, 360582345647127805, 360582345380242212, 360582345159046067, 360582345074389765, 360582345039505596, 360582345163908432]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 85660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 85600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569037653843872, 360569085724728755⟩, ⟨1133280109640369976, 1136061565098729350⟩, true⟩

def words07 : List Nat := [360582345202454088, 360582345241119524, 360582345275884323, 360582345385430213, 360582345415308462, 360582345445384310, 360582345446481292, 360582345408189277, 360582345233373313, 360582345080063708]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 85670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 85600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565377378220269, 360565425460693444⟩, ⟨1446857295359602424, 1449639743761922878⟩, true⟩

def words08 : List Nat := [360582344926306813, 360582344865922629, 360582344669121525, 360582344386841850, 360582344104366835, 360582343787926736, 360582343539885853, 360582343288421632, 360582343036839162, 360582342717593455]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 85680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 85600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592232811270718, 360592280905365136⟩, ⟨(-854511706181527539), (-851728261898891825)⟩, true⟩

def words09 : List Nat := [360582342521167248, 360582342461185133, 360582342436144943, 360582342476530499, 360582342477667342, 360582342401853226, 360582342325801609, 360582342300986354, 360582342417951982, 360582342535195606]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 85690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 85600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 85600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk856
