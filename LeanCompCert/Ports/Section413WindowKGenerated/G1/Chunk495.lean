import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk495

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486951524615209, 362486986901069948⟩, ⟨(-100591232716768139), (-99408159439786987)⟩, true⟩

def state01 : KState := ⟨⟨362478496251598124, 362478531642752759⟩, ⟨318017412928239713, 319201213925071365⟩, true⟩

def words00 : List Nat := [371284979069653336, 371284979071304676, 371284978965863190, 371284978820261288, 371284978673965861, 371284978654973460, 371284978580776232, 371284978715648942, 371284978847949740, 371284978849658942]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 49500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 49500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494146898679649, 362494182304797477⟩, ⟨(-456966359050683131), (-455781817150152677)⟩, true⟩

def words01 : List Nat := [371284978720589093, 371284978636252715, 371284978809301467, 371284978810956384, 371284978650511911, 371284978420160597, 371284978225230860, 371284978227100814, 371284978308228775, 371284978495965868]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 49510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 49500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484311333069559, 362484346754067631⟩, ⟨30079764676191348, 31265043523792454⟩, true⟩

def words02 : List Nat := [371284978627286924, 371284978628949624, 371284978567192058, 371284978741125809, 371284978943998398, 371284978945650082, 371284978605810412, 371284978264660011, 371284977986649523, 371284977988542168]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 49520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 49500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481023213411137, 362481058649296978⟩, ⟨193023831572720080, 194209847885548986⟩, true⟩

def words03 : List Nat := [371284978370907576, 371284978766690219, 371284979086295678, 371284979087947886, 371284978864846379, 371284978769079062, 371284978981252647, 371284978988715259, 371284978989972603, 371284978912677793]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 49530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 49500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362506747526830091, 362506782977496007⟩, ⟨(-1081463817618546383), (-1080277069023905775)⟩, true⟩

def words04 : List Nat := [371284979124793333, 371284979248211198, 371284979542608672, 371284979837686328, 371284980060034689, 371284980061716054, 371284980232738292, 371284980522866953, 371284981218587991, 371284981660286992]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 49540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 49500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499554624796198, 362499590090563360⟩, ⟨(-725018893865165407), (-723831396929124185)⟩, true⟩

def words05 : List Nat := [371284982115315583, 371284982570908385, 371284983196700760, 371284983620600779, 371284983996307518, 371284984372613370, 371284984749281296, 371284984750934572, 371284984935178407, 371284985231966296]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 49550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 49500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474167419711538, 362474202900191604⟩, ⟨533342306083688687, 534530532269271821⟩, true⟩

def words06 : List Nat := [371284985834323102, 371284985895184894, 371284985953860753, 371284986013065295, 371284986115741387, 371284986117575054, 371284986138883962, 371284986201556671, 371284986245913340, 371284986247624916]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 49560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 49500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362503699432645493, 362503734928047993⟩, ⟨(-930688809837111770), (-929499843871206420)⟩, true⟩

def words07 : List Nat := [371284986110599829, 371284986191965694, 371284986620794441, 371284986711214569, 371284986747150435, 371284986783612028, 371284987028924608, 371284987071275731, 371284987450531943, 371284987830493059]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 49570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 49500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487008543659043, 362487044054029931⟩, ⟨(-103122001843894972), (-101932293672018258)⟩, true⟩

def words08 : List Nat := [371284988129907742, 371284988131569493, 371284988321906247, 371284988603891126, 371284988973558202, 371284988975212235, 371284988803495338, 371284988633401445, 371284988551138966, 371284988594497516]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 49580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 49500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468101796281934, 362468137321546135⟩, ⟨834657485347786070, 835847932154341014⟩, true⟩

def words09 : List Nat := [371284988985985893, 371284989378144979, 371284989743598544, 371284989745252819, 371284989615562394, 371284989502692020, 371284989679748794, 371284989681403184, 371284989432246406, 371284989094371828]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 49590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 49500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 49500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk495
