import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk856A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk856B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk856A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk856B
