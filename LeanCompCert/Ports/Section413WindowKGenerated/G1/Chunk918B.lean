import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk918A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk918B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk918A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk918B
