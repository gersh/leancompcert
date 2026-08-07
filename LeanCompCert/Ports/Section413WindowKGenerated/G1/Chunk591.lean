import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk591

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489950442490327, 362490001593072251⟩, ⟨(-295868143370853299), (-293826132312687849)⟩, true⟩

def state01 : KState := ⟨⟨362477613634681359, 362477664803078517⟩, ⟨433297241256050590, 435340305287587480⟩, true⟩

def words00 : List Nat := [371285030202634079, 371285030204634007, 371285030098781473, 371285029950799946, 371285029802030588, 371285029739590887, 371285029613570417, 371285029695409329, 371285029719045987, 371285029721117556]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362509241890129394, 362509293076599485⟩, ⟨(-1436417572702660299), (-1434373440287186337)⟩, true⟩

def words01 : List Nat := [371285029662035968, 371285029728615678, 371285030080726354, 371285030178385987, 371285030195457999, 371285030213106451, 371285030468859649, 371285030594914107, 371285031006663893, 371285031419315489]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362504027351602056, 362504078556144681⟩, ⟨(-1128106286782468992), (-1126061085828049990)⟩, true⟩

def words02 : List Nat := [371285031832289315, 371285032042597691, 371285032538732210, 371285033035874979, 371285033530740704, 371285033803379888, 371285034074179591, 371285034345667269, 371285034733684631, 371285035058050145]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486468482950235, 362486519705480146⟩, ⟨(-89693626862617285), (-87647362229656479)⟩, true⟩

def words03 : List Nat := [371285035593116065, 371285036128957644, 371285036642728944, 371285036775634609, 371285036993503653, 371285037212441570, 371285037618982253, 371285037644857828, 371285037671426703, 371285037698712766]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489696932648906, 362489748173096564⟩, ⟨(-280626051394610403), (-278578727015330805)⟩, true⟩

def words04 : List Nat := [371285038011420978, 371285038182742479, 371285038388574291, 371285038595201946, 371285038758359246, 371285038760359023, 371285038542136843, 371285038424302713, 371285038471451208, 371285038553191316]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499573762678845, 362499625021347771⟩, ⟨(-864886853573053856), (-862838451315107042)⟩, true⟩

def words05 : List Nat := [371285038632943683, 371285038713394303, 371285039039369376, 371285039224016050, 371285039493375918, 371285039763477242, 371285039980086444, 371285039982099994, 371285040190390508, 371285040439421923]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 59150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 59100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491083676586072, 362491134953072495⟩, ⟨(-362553429925488377), (-360503973492886111)⟩, true⟩

def words06 : List Nat := [371285040928025903, 371285041036271730, 371285041096766885, 371285041157945799, 371285041303881338, 371285041347837484, 371285041676958765, 371285042006911291, 371285042269347023, 371285042374385421]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 59160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 59100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497296638322047, 362497347932889886⟩, ⟨(-730212078826717222), (-728161552424551528)⟩, true⟩

def words07 : List Nat := [371285042578851729, 371285042784301790, 371285043227978698, 371285043291457361, 371285043307788934, 371285043324754442, 371285043483575791, 371285043538329561, 371285043747604651, 371285043957755560]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 59170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 59100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475872358931662, 362475923671530304⟩, ⟨537767357213711657, 539818950770364689⟩, true⟩

def words08 : List Nat := [371285044165845405, 371285044167846458, 371285044171327861, 371285044317775581, 371285044460095731, 371285044462096998, 371285044256562984, 371285044055467726, 371285043853591409, 371285043775446006]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 59180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 59100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362463658516087687, 362463709846739406⟩, ⟨1260828131002992380, 1262880793212273910⟩, true⟩

def words09 : List Nat := [371285043622733653, 371285043615669390, 371285043607887582, 371285043601965095, 371285043304703262, 371285043093990023, 371285042954957422, 371285042956959017, 371285042650640943, 371285042292570695]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 59190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 59100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 59100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk591
