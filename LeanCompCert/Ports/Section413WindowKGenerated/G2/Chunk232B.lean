import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk232A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk232B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk232A

def state06 : KState := ⟨⟨360591685913143173, 360591689095702149⟩, ⟨(-253012727820868512), (-252962645125433992)⟩, true⟩

def words05 : List Nat := [360580800037684920, 360580802443758078, 360580803635242715, 360580805896572516, 360580807683812275, 360580809470982500, 360580811797122302, 360580813191378750, 360580813659227708, 360580814127079759]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360648063335005839, 360648066520420148⟩, ⟨(-1564832037992478100), (-1564781888868012548)⟩, true⟩

def words06 : List Nat := [360580814529294884, 360580815856601889, 360580818291858955, 360580820726964188, 360580821332853580, 360580821333155769, 360580820104910122, 360580820095290899, 360580821918091949, 360580824808037010]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360609642787878831, 360609645976170064⟩, ⟨(-670696216184644137), (-670646000099889843)⟩, true⟩

def words07 : List Nat := [360580826772816226, 360580828737459497, 360580830757117555, 360580833734918897, 360580835305788332, 360580836876569140, 360580837523259336, 360580837523561664, 360580838157952051, 360580839395692427]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603204803993261, 360603207995135562⟩, ⟨(-520741786461906900), (-520691503989884798)⟩, true⟩

def words08 : List Nat := [360580841709171594, 360580844071665669, 360580845306683342, 360580846541624127, 360580847305239759, 360580848991035814, 360580850170848833, 360580851350616525, 360580851350890667, 360580852084956099]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360730332996294532, 360730336190292628⟩, ⟨(-3482216213629149346), (-3482165864631227596)⟩, true⟩

def words09 : List Nat := [360580854884037947, 360580857682970689, 360580862320440746, 360580866209221333, 360580868529044913, 360580870848699534, 360580875006585220, 360580880596591287, 360580887011239683, 360580893425405661]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk232B
