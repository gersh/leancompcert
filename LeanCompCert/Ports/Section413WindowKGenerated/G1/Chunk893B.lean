import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk893A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk893B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk893A

def state06 : KState := ⟨⟨362486593397622549, 362486714161806592⟩, ⟨(-147912113138131298), (-140625826202412994)⟩, true⟩

def words05 : List Nat := [371285140915296185, 371285140905622517, 371285140945017402, 371285140948134168, 371285140855522677, 371285140720066115, 371285140583376438, 371285140540214365, 371285140458328180, 371285140479482062]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478178326797221, 362478299119143992⟩, ⟨604123439967176854, 611412243668727168⟩, true⟩

def words06 : List Nat := [371285140500114061, 371285140503299734, 371285140521752190, 371285140596186272, 371285140700600632, 371285140703716957, 371285140641442646, 371285140580115638, 371285140517536164, 371285140478030294]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476122698138834, 362476243518530731⟩, ⟨787878413575952041, 795169723806501573⟩, true⟩

def words07 : List Nat := [371285140452114926, 371285140503989332, 371285140556808137, 371285140559924598, 371285140445827852, 371285140332330260, 371285140217097793, 371285140218656201, 371285140120789511, 371285140024726821]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491864521684028, 362491985370004823⟩, ⟨(-619200046814002323), (-611906240154224627)⟩, true⟩

def words08 : List Nat := [371285139952811493, 371285139956246369, 371285139934912864, 371285139951777157, 371285139954189578, 371285139936779228, 371285139855561676, 371285139880157493, 371285140012205771, 371285140092066841]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492643084807793, 362492763961523869⟩, ⟨(-688776715615319265), (-681480370559454313)⟩, true⟩

def words09 : List Nat := [371285140168927454, 371285140246882262, 371285140448529657, 371285140598946285, 371285140776150597, 371285140954512675, 371285141083916881, 371285141087034408, 371285141134690934, 371285141223852485]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk893B
