import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk893

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487369590993695, 362487490186856801⟩, ⟨(-216674812854155927), (-209403562042942569)⟩, true⟩

def state01 : KState := ⟨⟨362476250451203369, 362476371075132917⟩, ⟨776295361968345051, 783569119257507381⟩, true⟩

def words00 : List Nat := [371285145278246042, 371285145281359508, 371285145123906827, 371285145093355683, 371285145061236690, 371285145057591576, 371285144948821102, 371285144841657223, 371285144733273301, 371285144662852742]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 89300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 89300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362470815064806079, 362470935716859821⟩, ⟨1261768019819512626, 1269044289017613594⟩, true⟩

def words01 : List Nat := [371285144566730710, 371285144545394045, 371285144523002508, 371285144477368010, 371285144263779436, 371285144089996417, 371285143914597435, 371285143865441030, 371285143712537852, 371285143557086172]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 89310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 89300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476393381685208, 362476514061563980⟩, ⟨763517251616005881, 770796006291787587⟩, true⟩

def words02 : List Nat := [371285143400133072, 371285143360754061, 371285143257529239, 371285143238989627, 371285143219533977, 371285143179912513, 371285142988447941, 371285142850309510, 371285142710516151, 371285142697031257]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 89320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 89300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477159696043591, 362477280404265503⟩, ⟨695066406649451138, 702347693364361846⟩, true⟩

def words03 : List Nat := [371285142602783358, 371285142485876661, 371285142367727733, 371285142362062538, 371285142311488627, 371285142273379098, 371285142234174157, 371285142183879242, 371285142002802372, 371285141918630450]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 89330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 89300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472959400959281, 362473080136963953⟩, ⟨1070358647030895991, 1077642416001492195⟩, true⟩

def words04 : List Nat := [371285141832785136, 371285141799926576, 371285141678048089, 371285141558915121, 371285141438546192, 371285141348455338, 371285141194552552, 371285141147998364, 371285141100376022, 371285141048167104]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 89340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 89300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk893
