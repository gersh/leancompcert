import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk522A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk522B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk522A

def state06 : KState := ⟨⟨360602102784813639, 360602119980026442⟩, ⟨(-1050731478578246047), (-1050124297031307041)⟩, true⟩

def words05 : List Nat := [360582024856279081, 360582024695351322, 360582024738320045, 360582025125232023, 360582025260453227, 360582025395778018, 360582025396422633, 360582025367214573, 360582025752311886, 360582026137638595]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 52250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 52200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360610048238822304, 360610065440853894⟩, ⟨(-1466017856440245888), (-1465410318508682866)⟩, true⟩

def words06 : List Nat := [360582026577937665, 360582027028094955, 360582027294397643, 360582027560763444, 360582027735160807, 360582028112568768, 360582028855224621, 360582029597990840, 360582030040860237, 360582030577956520]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 52260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 52200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360630621797897463, 360630639006762359⟩, ⟨(-2541532503346517844), (-2540924608204426202)⟩, true⟩

def words07 : List Nat := [360582031404011986, 360582032230261697, 360582033164988836, 360582033862699013, 360582034185539868, 360582034508434550, 360582035084511617, 360582035845301391, 360582036775557724, 360582037705941709]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 52270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 52200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600565545992318, 360600582761767297⟩, ⟨(-970309676513911334), (-969701420079398988)⟩, true⟩

def words08 : List Nat := [360582038386143217, 360582038701439376, 360582038784071308, 360582038866898093, 360582038867503902, 360582038858557857, 360582038745987915, 360582038402212422, 360582038078952114, 360582038434443678]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 52280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 52200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571338774047401, 360571355996636860⟩, ⟨558259564330031468, 558868177128476090⟩, true⟩

def words09 : List Nat := [360582039154762876, 360582039875195196, 360582040412387422, 360582040895806880, 360582041287467376, 360582041679304796, 360582041974230336, 360582042015559574, 360582042016214354, 360582041812643141]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 52290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 52200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 52200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk522B
