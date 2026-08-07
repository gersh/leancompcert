import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk582

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360631576211439046, 360631597724089740⟩, ⟨(-2890251318225594603), (-2889405437625707593)⟩, true⟩

def state01 : KState := ⟨⟨360604749734082060, 360604771254378559⟩, ⟨(-1328957667516777271), (-1328111341892079677)⟩, true⟩

def words00 : List Nat := [360581953135922223, 360581953542015790, 360581953750672498, 360581953959403397, 360581953967927354, 360581954139680900, 360581954606441297, 360581955073343605, 360581955391281892, 360581955784074114]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360636896254651831, 360636917782634246⟩, ⟨(-3200349825123215475), (-3199503052064953039)⟩, true⟩

def words01 : List Nat := [360581956471881906, 360581957159935709, 360581957984158798, 360581958724005454, 360581959214266843, 360581959704576555, 360581960489871118, 360581961442951384, 360581962387562544, 360581963332314517]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360624930276494088, 360624951812221329⟩, ⟨(-2503823231259016073), (-2502976007258142397)⟩, true⟩

def words02 : List Nat := [360581964129642722, 360581964740696242, 360581965304917595, 360581965869353486, 360581966243789940, 360581966625341232, 360581966821056740, 360581967016850924, 360581967507537477, 360581968246641859]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360615610916022850, 360615632459418982⟩, ⟨(-1961044030182694418), (-1960196359583868096)⟩, true⟩

def words03 : List Nat := [360581969280487155, 360581970314453431, 360581971097850016, 360581971838944734, 360581972438506283, 360581973038262573, 360581973932754102, 360581974662198779, 360581975240846083, 360581975819601949]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360635047015105781, 360635068566171117⟩, ⟨(-3093015865375726772), (-3092167748084232308)⟩, true⟩

def words04 : List Nat := [360581976628654442, 360581977648500527, 360581978963005596, 360581980277621346, 360581981296234213, 360581982020971693, 360581982668354043, 360581983315949482, 360581984140468421, 360581985052616256]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk582
