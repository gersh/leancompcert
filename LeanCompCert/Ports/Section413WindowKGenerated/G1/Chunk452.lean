import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk452

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496398945814972, 362496428225739564⟩, ⟨(-492940885041826324), (-492046697411766170)⟩, true⟩

def state01 : KState := ⟨⟨362485520252765755, 362485549546177304⟩, ⟨(-1270137974932327), (-375340663745239)⟩, true⟩

def words00 : List Nat := [371285542686427724, 371285542687923908, 371285542299462332, 371285542216452400, 371285542196180173, 371285542197702276, 371285541855986423, 371285541514465856, 371285541242299249, 371285541244200712]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 45200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 45200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484070671710929, 362484099978611984⟩, ⟨64344991267857781, 65240398506133401⟩, true⟩

def words01 : List Nat := [371285541609049472, 371285541974475636, 371285542242929574, 371285542244434697, 371285542216268522, 371285542277611534, 371285542770730514, 371285542772229548, 371285542742084342, 371285542711882797]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 45210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 45200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476237832473302, 362476267152750838⟩, ⟨418648701931642172, 419544714124887650⟩, true⟩

def words02 : List Nat := [371285542901539380, 371285542903188783, 371285543233080087, 371285543586754152, 371285543841190426, 371285543842687709, 371285543445632124, 371285543148881507, 371285542957394265, 371285542958944181]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 45220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 45200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480794327285555, 362480823661228683⟩, ⟨212599900802249430, 213496531157137788⟩, true⟩

def words03 : List Nat := [371285542754987593, 371285542551003248, 371285542629250728, 371285542739216499, 371285542986361880, 371285543234055829, 371285543422826834, 371285543424324468, 371285542961969355, 371285542859530123]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 45230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 45200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362457191819378654, 362457221166670737⟩, ⟨1280455539451929168, 1281352773782909234⟩, true⟩

def words04 : List Nat := [371285542777463002, 371285542778960738, 371285542150410854, 371285541432594220, 371285540714250248, 371285540144600941, 371285539330852606, 371285539005994772, 371285538680596664, 371285538355041631]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 45240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 45200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498556637278457, 362498585998090234⟩, ⟨(-591535776554948591), (-590637930389584269)⟩, true⟩

def words05 : List Nat := [371285537730278388, 371285537484103844, 371285537247519451, 371285537249031588, 371285536925161882, 371285536479323723, 371285536032883789, 371285536018625746, 371285536108431264, 371285536398426295]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 45250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 45200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482639677265461, 362482669051624873⟩, ⟨128970660454624458, 129869119853944800⟩, true⟩

def words06 : List Nat := [371285536661178681, 371285536662703619, 371285537001863931, 371285537416635268, 371285537846763993, 371285537848269614, 371285537814050524, 371285537786864370, 371285537817734266, 371285537819459067]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 45260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 45200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362460277286448186, 362460306674320850⟩, ⟨1141509649883989602, 1142408721096187128⟩, true⟩

def words07 : List Nat := [371285537997707288, 371285538239932770, 371285538481123491, 371285538482622219, 371285538073765091, 371285537814795965, 371285537653327793, 371285537654826576, 371285537104407965, 371285536548903363]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 45270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 45200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362466858064698018, 362466887465996369⟩, ⟨843547132614883528, 844446811811258104⟩, true⟩

def words08 : List Nat := [371285535992736032, 371285535924640904, 371285535612741061, 371285535504651848, 371285535396115216, 371285535211916173, 371285534377628741, 371285533686963449, 371285532995517570, 371285532791936119]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 45280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 45200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484866839947335, 362484896254882585⟩, ⟨27851698659039815, 28751995539500685⟩, true⟩

def words09 : List Nat := [371285532381379789, 371285531981712524, 371285531667420504, 371285531669072228, 371285531513118933, 371285531505442540, 371285531497268386, 371285531392751646, 371285530968940820, 371285530956770875]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 45290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 45200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 45200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk452
