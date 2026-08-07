import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk918

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476797391842754, 362476925106590503⟩, ⟨742236149180028930, 750152060166506786⟩, true⟩

def state01 : KState := ⟨⟨362474340086286140, 362474467829597571⟩, ⟨967846355782488320, 975764889060874940⟩, true⟩

def words00 : List Nat := [371285096640381189, 371285096643589881, 371285096527379998, 371285096408090342, 371285096287643078, 371285096167117338, 371285096017054490, 371285095986916561, 371285095955665063, 371285095919011153]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 91800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 91800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482396254345575, 362482524026662250⟩, ⟨228220926345119959, 236142122745789445⟩, true⟩

def words01 : List Nat := [371285095808224498, 371285095814894513, 371285095938421401, 371285095941633623, 371285095937139045, 371285095914728468, 371285095894865735, 371285095898436053, 371285095845070500, 371285095820636829]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 91810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 91800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481484477371829, 362481612278629419⟩, ⟨311910216757495552, 319834070663465424⟩, true⟩

def words02 : List Nat := [371285095795027091, 371285095766102958, 371285095601857892, 371285095557866105, 371285095512246391, 371285095503407966, 371285095396052136, 371285095286563412, 371285095175776007, 371285095171699914]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 91820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 91800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479655715721254, 362479783545969889⟩, ⟨479904716390039662, 487831232687551718⟩, true⟩

def words03 : List Nat := [371285095206402752, 371285095280383462, 371285095330292839, 371285095333513788, 371285095287282848, 371285095279001522, 371285095375430163, 371285095378641369, 371285095351314979, 371285095297196888]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 91830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 91800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490734111860610, 362490861970810522⟩, ⟨(-537565556306113525), (-529636403935481331)⟩, true⟩

def words04 : List Nat := [371285095302195456, 371285095307273392, 371285095398824217, 371285095491649024, 371285095570850922, 371285095574068268, 371285095533499040, 371285095540681105, 371285095648418948, 371285095714548364]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 91840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 91800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362495967992896859, 362496095881050214⟩, ⟨(-1018320604401208434), (-1010388769543434668)⟩, true⟩

def words05 : List Nat := [371285095765967331, 371285095818434033, 371285095969669973, 371285096079153048, 371285096223598738, 371285096369313654, 371285096506410121, 371285096530614682, 371285096652532334, 371285096776211998]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486072343310973, 362486200260073358⟩, ⟨(-109274034652240571), (-101339571619219989)⟩, true⟩

def words06 : List Nat := [371285096912166877, 371285096921244079, 371285096923667146, 371285096922784888, 371285096942614905, 371285096946154481, 371285097001544825, 371285097090888954, 371285097180971909, 371285097196303298]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500765504688539, 362500893450508280⟩, ⟨(-1459226609234419075), (-1451289476563232065)⟩, true⟩

def words07 : List Nat := [371285097264785199, 371285097335033555, 371285097521920697, 371285097567123067, 371285097582324964, 371285097598450575, 371285097720250713, 371285097784350734, 371285097958444720, 371285098133994929]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482912339649202, 362483040314515489⟩, ⟨181199357285091338, 189139158899342938⟩, true⟩

def words08 : List Nat := [371285098299597765, 371285098367473578, 371285098494739098, 371285098623647820, 371285098740887687, 371285098744099681, 371285098703652954, 371285098665024972, 371285098632275734, 371285098635974836]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478289718801310, 362478417722541129⟩, ⟨606047533184709778, 613989988139077724⟩, true⟩

def words09 : List Nat := [371285098691426137, 371285098770553310, 371285098848384847, 371285098851618896, 371285098828971167, 371285098838618821, 371285098925425737, 371285098928638016, 371285098857905580, 371285098788788562]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk918
