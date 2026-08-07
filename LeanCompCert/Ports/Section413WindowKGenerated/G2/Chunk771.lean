import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk771

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592071479175735, 360592110085766902⟩, ⟨(-768915910736053597), (-766905518429762035)⟩, true⟩

def state01 : KState := ⟨⟨360601927507424487, 360601966124365878⟩, ⟨(-1528890882147836401), (-1526879691786510127)⟩, true⟩

def words00 : List Nat := [360582163618705377, 360582163844160890, 360582163965158553, 360582164086259403, 360582164090802411, 360582164193415921, 360582164424992269, 360582164656773803, 360582164804431018, 360582165062367117]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 77100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 77100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360604298701478230, 360604337328815718⟩, ⟨(-1711735061980747779), (-1709723069925987871)⟩, true⟩

def words01 : List Nat := [360582165410451577, 360582165758886313, 360582166221214474, 360582166516066324, 360582166654432131, 360582166792884764, 360582167051026580, 360582167393681129, 360582167682060595, 360582167970665202]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 77110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 77100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360588030409618426, 360588069047443097⟩, ⟨(-457138311328667558), (-455125510451313912)⟩, true⟩

def words02 : List Nat := [360582168108695696, 360582168109795871, 360582168185113947, 360582168291366238, 360582168351406272, 360582168419343403, 360582168420324056, 360582168388064286, 360582168355600507, 360582168365350926]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 77120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 77100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565594970820636, 360565633619017258⟩, ⟨1273464719250495515, 1275478320168550003⟩, true⟩

def words03 : List Nat := [360582168574285719, 360582168783433227, 360582168862840547, 360582168863940903, 360582168775670804, 360582168645644324, 360582168551808939, 360582168552909340, 360582168422819510, 360582168209633911]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 77130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 77100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585131973218198, 360585170631800817⟩, ⟨(-233682129811586326), (-231667727667132700)⟩, true⟩

def words04 : List Nat := [360582167996181147, 360582168032177101, 360582168141111136, 360582168250247133, 360582168251262781, 360582168202504897, 360582168097721553, 360582167956125999, 360582167814199794, 360582167848587805]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 77140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 77100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360581064753769994, 360581103422831919⟩, ⟨80175399816959651, 82190610492119099⟩, true⟩

def words05 : List Nat := [360582167849568547, 360582167805694863, 360582167884311148, 360582168167369810, 360582168357288975, 360582168547378370, 360582168652405195, 360582168653506016, 360582168632510679, 360582168619961159]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 77150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 77100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360564617317672405, 360564655997118532⟩, ⟨1349270371993557157, 1351286383964914147⟩, true⟩

def words06 : List Nat := [360582168607061983, 360582168554782051, 360582168405015261, 360582168133767402, 360582167862354770, 360582167442379385, 360582167109483222, 360582166944454410, 360582166779286037, 360582166511359363]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 77160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 77100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594871552727978, 360594910242562288⟩, ⟨(-985622134972310394), (-983605321295877038)⟩, true⟩

def words07 : List Nat := [360582166285344192, 360582166227271561, 360582166242924509, 360582166244025953, 360582166208351225, 360582166013942035, 360582165819319732, 360582165772198300, 360582165938215173, 360582166104480431]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 77170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 77100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582484024902934, 360582522725237166⟩, ⟨(-29510392429884504), (-27492768318456648)⟩, true⟩

def words08 : List Nat := [360582166163001259, 360582166280683805, 360582166523609336, 360582166766863235, 360582166935950038, 360582166937859632, 360582166938847540, 360582166812277942, 360582166685514680, 360582166559773337]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 77180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 77100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575264046704599, 360575302757413498⟩, ⟨527893188735419911, 529911613719459619⟩, true⟩

def words09 : List Nat := [360582166732797076, 360582166906027320, 360582166992402897, 360582167028823291, 360582167029745111, 360582167024310932, 360582167018536936, 360582166989364541, 360582166985260872, 360582166897487585]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 77190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 77100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 77100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk771
