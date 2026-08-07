import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk221

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362520330668011949, 362520337263605814⟩, ⟨(-803609723558133946), (-803511154029314778)⟩, true⟩

def state01 : KState := ⟨⟨362511303941333094, 362511310543157791⟩, ⟨(-604293736631904601), (-604195029369595997)⟩, true⟩

def words00 : List Nat := [371283982567070133, 371283982567761518, 371283982355900808, 371283982858849635, 371283983982239781, 371283983982942882, 371283983421552939, 371283982855024066, 371283983765821636, 371283985002505193]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 22100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 22100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362469643220034530, 362469649828097802⟩, ⟨317269615888921783, 317368461117875859⟩, true⟩

def words01 : List Nat := [371283988283356909, 371283991564201347, 371283994529657713, 371283994771864664, 371283995634450338, 371283996497292276, 371283998637127510, 371283998637819280, 371283998055572615, 371283997407714343]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 22110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 22100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362500300893135925, 362500307507389234⟩, ⟨(-360944022859931429), (-360845040675292223)⟩, true⟩

def words02 : List Nat := [371283997142572323, 371283997143341100, 371283997907922286, 371283999311604766, 371284000251742555, 371284000252439075, 371283999792483304, 371283999785428409, 371284001811206532, 371284002548703441]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 22120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 22100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362506770561140952, 362506777181700307⟩, ⟨(-503994112813942999), (-503894991045102371)⟩, true⟩

def words03 : List Nat := [371284003294301707, 371284004040059188, 371284006826107085, 371284009052122905, 371284011703139756, 371284014354186102, 371284016869773621, 371284016870466233, 371284017696152726, 371284018724943833]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 22130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 22100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362452401346020639, 362452407972754361⟩, ⟨699973102360868598, 700072360862374178⟩, true⟩

def words04 : List Nat := [371284020581075072, 371284020581767741, 371284019721208509, 371284018347698305, 371284016974038683, 371284015995202368, 371284014048872860, 371284014095531036, 371284014096054964, 371284013948414062]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 22140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 22100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362553600671996471, 362553607305000647⟩, ⟨(-1542126275121451508), (-1542026877697829574)⟩, true⟩

def words05 : List Nat := [371284012522044160, 371284012370676080, 371284014104112063, 371284014710857603, 371284014797750677, 371284014884836016, 371284017008217547, 371284018112998745, 371284021253776211, 371284024394586053]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 22150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 22100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362496158134024548, 362496164773285476⟩, ⟨(-268915362612105503), (-268815826506240179)⟩, true⟩

def words06 : List Nat := [371284027495983020, 371284028921409460, 371284031869113536, 371284034816901074, 371284037789080522, 371284038050211928, 371284038279886149, 371284038509775466, 371284039566067488, 371284040113752472]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 22160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 22100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486754554899208, 362486761200407231⟩, ⟨(-60217967944916128), (-60118293310097216)⟩, true⟩

def words07 : List Nat := [371284042695022113, 371284045276334515, 371284047789701926, 371284047790395690, 371284048001223413, 371284048408898418, 371284050474084194, 371284050603809199, 371284050726537414, 371284050849507358]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 22170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 22100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492283025442462, 362492289677162486⟩, ⟨(-182835318710885477), (-182735506261573587)⟩, true⟩

def words08 : List Nat := [371284052471782979, 371284053084068381, 371284054523111275, 371284055962303656, 371284056837309734, 371284056838003802, 371284055007102091, 371284054207633234, 371284054637844156, 371284055009672893]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 22180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 22100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362509461325086753, 362509467983138120⟩, ⟨(-564063684250099823), (-563963731277069655)⟩, true⟩

def words09 : List Nat := [371284055317660455, 371284055625861732, 371284057963338147, 371284059312232934, 371284060931558965, 371284062550997343, 371284063708960992, 371284063709660024, 371284064210593041, 371284065355721469]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 22190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 22100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 22100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk221
