import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk814

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481762045425616, 362481861534989239⟩, ⟨265929635548919186, 271398075754231064⟩, true⟩

def state01 : KState := ⟨⟨362496466153063306, 362496565667867801⟩, ⟨(-931059799557339045), (-925589304618588241)⟩, true⟩

def words00 : List Nat := [371285195734559047, 371285195772137408, 371285195840558225, 371285195910064581, 371285195948258588, 371285195951092503, 371285195923852807, 371285195980083552, 371285196185663316, 371285196328286927]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 81400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 81400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487894100286844, 362487993640712741⟩, ⟨(-233146737341753230), (-227674156431939008)⟩, true⟩

def words01 : List Nat := [371285196441842321, 371285196556306935, 371285196764559351, 371285196898860116, 371285197065566675, 371285197233369689, 371285197370977582, 371285197373796053, 371285197344488097, 371285197382297444]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 81410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 81400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492502317556816, 362492601883077527⟩, ⟨(-608343818319493842), (-602869194057895588)⟩, true⟩

def words02 : List Nat := [371285197569362512, 371285197622344029, 371285197675792207, 371285197730261958, 371285197827781259, 371285197857409788, 371285198022241853, 371285198188191656, 371285198353268534, 371285198447112626]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 81420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 81400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362503705676366347, 362503805267450143⟩, ⟨(-1520721642724140877), (-1515244936738671545)⟩, true⟩

def words03 : List Nat := [371285198602294137, 371285198758979975, 371285198992407794, 371285199070104788, 371285199115417694, 371285199161581390, 371285199293150731, 371285199374035912, 371285199604409362, 371285199836073580]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 81430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 81400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489630214167525, 362489729830686415⟩, ⟨(-374384333359740540), (-368905555810791594)⟩, true⟩

def words04 : List Nat := [371285200066301503, 371285200121239821, 371285200282759289, 371285200445726070, 371285200608837492, 371285200611657277, 371285200588858300, 371285200548821306, 371285200600231053, 371285200659088635]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 81440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 81400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483235580375416, 362483335222288833⟩, ⟨146533720472415610, 152014566537963846⟩, true⟩

def words05 : List Nat := [371285200844596571, 371285201031274412, 371285201210246965, 371285201213067035, 371285201206876819, 371285201207635546, 371285201354918786, 371285201365184026, 371285201367351028, 371285201347583923]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362502385682545676, 362502485349688687⟩, ⟨(-1413512744392567997), (-1408029842995381653)⟩, true⟩

def words06 : List Nat := [371285201400332845, 371285201403440611, 371285201552848423, 371285201705017734, 371285201831572407, 371285201890480438, 371285202061965809, 371285202234912338, 371285202545210256, 371285202760264286]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495482715321593, 362495582408224532⟩, ⟨(-851079262620392443), (-845594262435915237)⟩, true⟩

def words07 : List Nat := [371285202972533326, 371285203185787344, 371285203450059731, 371285203645178656, 371285203883425856, 371285204122719833, 371285204330843999, 371285204338903866, 371285204468186756, 371285204599134856]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482803624792170, 362482903342816931⟩, ⟨182087284048854525, 187574331289342675⟩, true⟩

def words08 : List Nat := [371285204823210877, 371285204863373705, 371285204896323819, 371285204930214800, 371285204996808834, 371285204999949879, 371285205046261129, 371285205103116919, 371285205147861684, 371285205150784650]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499448238199466, 362499547981678483⟩, ⟨(-1174343576201718194), (-1168854454563503256)⟩, true⟩

def words09 : List Nat := [371285205207496187, 371285205293879880, 371285205510689217, 371285205603496220, 371285205672513571, 371285205742413159, 371285205910941798, 371285206028179998, 371285206206082860, 371285206385200360]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk814
