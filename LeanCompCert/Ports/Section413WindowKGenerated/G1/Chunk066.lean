import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk066

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362701133962569799, 362701134489539442⟩, ⟨(-1442491909075804050), (-1442489553487609350)⟩, true⟩

def state01 : KState := ⟨⟨362541566683832388, 362541567212460306⟩, ⟨(-388827218195342407), (-388824851653860119)⟩, true⟩

def words00 : List Nat := [371282644331684352, 371282649609424643, 371282654821896964, 371282660032852576, 371282672093609261, 371282672832736089, 371282696469555132, 371282720099302180, 371282743482819387, 371282752380868435]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 6600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 6600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362643888612623785, 362643889142931541⟩, ⟨(-1065986918469777361), (-1065984540815952851)⟩, true⟩

def words01 : List Nat := [371282772360358427, 371282792333899212, 371282826254248817, 371282829815868159, 371282829816016250, 371282827721509519, 371282838431726945, 371282839959818120, 371282864287616056, 371282888608145867]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 6610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 6600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362544520899814451, 362544521431809172⟩, ⟨(-407594048366831472), (-407591659536940266)⟩, true⟩

def words02 : List Nat := [371282912699822836, 371282925236411108, 371282954504827375, 371282983764508404, 371283018813642582, 371283023621062223, 371283027560026797, 371283031497864067, 371283044559870123, 371283053831215455]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 6620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 6600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362444844697478769, 362444845231158324⟩, ⟨254243492558309813, 254245892567377889⟩, true⟩

def words03 : List Nat := [371283078908704594, 371283103978709221, 371283123293978846, 371283123294166120, 371283120228869852, 371283122106123192, 371283146635113035, 371283146635300345, 371283141042448770, 371283135275219677]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 6630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 6600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362423477208433836, 362423477743792922⟩, ⟨396349566422173445, 396351977591842041⟩, true⟩

def words04 : List Nat := [371283139229424004, 371283139229632127, 371283143072000092, 371283147495482016, 371283148640100296, 371283148640287825, 371283119743827245, 371283100271977383, 371283080805886962, 371283079544934553]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 6640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 6600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362428666674099223, 362428667211164673⟩, ⟨362092338385524387, 362094760911202411⟩, true⟩

def words05 : List Nat := [371283070583746746, 371283061599577187, 371283066171806111, 371283068549919690, 371283071962800144, 371283075374729355, 371283075374872044, 371283074634327709, 371283043958329226, 371283035793884073]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 6650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 6600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362410770707797416, 362410771246536129⟩, ⟨481497931670206612, 481500365348388464⟩, true⟩

def words06 : List Nat := [371283041967505211, 371283041967693001, 371283026390545458, 371283010600945378, 371282994816006477, 371282983769532835, 371282964749705888, 371282963411419323, 371282962073474969, 371282960206858227]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 6660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 6600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362606245128390291, 362606245668832651⟩, ⟨(-823508378795230091), (-823505933745066513)⟩, true⟩

def words07 : List Nat := [371282949385678130, 371282947564561182, 371282966321846312, 371282966322034658, 371282962988909035, 371282955569808075, 371282951785425748, 371282951785638243, 371282966337220920, 371282984789661110]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 6670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 6600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472363687499056, 362472364229640249⟩, ⟨70989796853960704, 70992253261139770⟩, true⟩

def words08 : List Nat := [371283000438824784, 371283000439014077, 371283005365370480, 371283015532826667, 371283026827812249, 371283026828000852, 371283008426401544, 371282990152561324, 371282975926475124, 371282975926689747]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 6680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 6600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362326600466000070, 362326601009842350⟩, ⟨1047691708380376064, 1047694176176452832⟩, true⟩

def words09 : List Nat := [371282995051429477, 371283015756024238, 371283033175674268, 371283033175863152, 371283020955950176, 371283012068453264, 371283010910823470, 371283010911012958, 371282996617360843, 371282973274943314]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 6690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 6600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 6600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk066
