import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk582A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk582B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk582A

def state06 : KState := ⟨⟨360609562624015035, 360609584182825789⟩, ⟨(-1608354505839148860), (-1607505937338895038)⟩, true⟩

def words05 : List Nat := [360581985815938844, 360581986579324048, 360581987428909451, 360581988513579468, 360581989476119135, 360581990438763902, 360581991254242544, 360581991775989733, 360581992250258216, 360581992724777715]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576770397749274, 360576791964230137⟩, ⟨302176453830307090, 303025469229458398⟩, true⟩

def words06 : List Nat := [360581993045975157, 360581993073539479, 360581993074264206, 360581992953214823, 360581992832037128, 360581992582740491, 360581992524364101, 360581992510013463, 360581992495560382, 360581992332674096]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597668269728702, 360597689843889047⟩, ⟨(-915665298162538551), (-914815835242619605)⟩, true⟩

def words07 : List Nat := [360581992449484775, 360581992655771627, 360581992990370180, 360581993031463884, 360581993032235530, 360581992777131734, 360581992521878689, 360581992664409232, 360581992934410957, 360581993204585628]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360589231101876549, 360589252683790694⟩, ⟨(-423907026100188280), (-423057111250433260)⟩, true⟩

def words08 : List Nat := [360581993326187317, 360581993551223576, 360581994006267931, 360581994461543734, 360581994841289401, 360581995001477708, 360581995013200824, 360581995025012478, 360581995025686424, 360581995009171106]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360555229459901375, 360555251049482431⟩, ⟨1558273033059276598, 1559123394850768044⟩, true⟩

def words09 : List Nat := [360581995340850751, 360581995672680686, 360581995791608656, 360581995792422668, 360581995617827989, 360581995318705711, 360581995019339419, 360581994928492322, 360581994618760244, 360581994160886390]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk582B
