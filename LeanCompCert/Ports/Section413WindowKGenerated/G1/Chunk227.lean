import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk227

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362537721944455184, 362537728918917253⟩, ⟨(-1218112545166519512), (-1218005488429401628)⟩, true⟩

def state01 : KState := ⟨⟨362487324288459181, 362487331269342922⟩, ⟨(-74030637320772600), (-73923434779210486)⟩, true⟩

def words00 : List Nat := [371284076551926228, 371284076552637115, 371284076880147290, 371284077893380319, 371284079307656414, 371284079308367399, 371284078139935936, 371284076835259491, 371284076163522570, 371284076307660072]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 22700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 22700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362449701783100237, 362449708770391660⟩, ⟨780689293634775907, 780796641727295333⟩, true⟩

def words01 : List Nat := [371284077736287029, 371284079165082211, 371284080497419877, 371284080498131480, 371284079644662663, 371284078397403696, 371284077839041928, 371284077839753775, 371284076331611472, 371284074819763460]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 22710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 22700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489687741398012, 362489694735069387⟩, ⟨(-127730667685603576), (-127623174607568908)⟩, true⟩

def words02 : List Nat := [371284073731847061, 371284073732644105, 371284074773651334, 371284076093546150, 371284077019128039, 371284077019844585, 371284077369186784, 371284078512170617, 371284079988419445, 371284080236164475]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 22720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 22700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362497219407564141, 362497226407713667⟩, ⟨(-298894835601274748), (-298787195241723814)⟩, true⟩

def words03 : List Nat := [371284080479995939, 371284080724038840, 371284082635262368, 371284083594620876, 371284085139414519, 371284086684367214, 371284087904741611, 371284087905453793, 371284087128246562, 371284087706898324]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 22730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 22700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489182116799852, 362489189123304342⟩, ⟨(-116050480370688920), (-115942695466840536)⟩, true⟩

def words04 : List Nat := [371284090218172935, 371284090469155864, 371284090469704208, 371284090331500658, 371284090640026575, 371284090640813180, 371284091120497803, 371284091931740578, 371284092740331616, 371284092965092974]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 22740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 22700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362525609122836259, 362525616135782040⟩, ⟨(-944806039528474457), (-944698108052860819)⟩, true⟩

def words05 : List Nat := [371284095120859910, 371284097276822760, 371284101027741267, 371284102633829027, 371284103666780359, 371284104699854956, 371284106513744461, 371284107363977521, 371284109188224818, 371284111012630472]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 22750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 22700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483775622446261, 362483782641834487⟩, ⟨7338463498448982, 7446541636772906⟩, true⟩

def words06 : List Nat := [371284112835335781, 371284112836050213, 371284113222594674, 371284113762033008, 371284114614778470, 371284114615491631, 371284112899306600, 371284111181690847, 371284109674017781, 371284109674844447]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 22760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 22700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470399133755285, 362470406159560540⟩, ⟨312028816804665844, 312137041091851036⟩, true⟩

def words07 : List Nat := [371284110427801971, 371284111195327948, 371284111961401946, 371284111962115397, 371284110462325450, 371284109530939761, 371284109594009957, 371284109594735624, 371284109000903756, 371284108400170367]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 22770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 22700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491278786472200, 362491285818662009⟩, ⟨(-163669343967548591), (-163560974207725479)⟩, true⟩

def words08 : List Nat := [371284107814257492, 371284107815043281, 371284107848175484, 371284108828398703, 371284109492084847, 371284109492798503, 371284107616185462, 371284107641421449, 371284108943231967, 371284109258870525]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 22780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 22700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362462254349458546, 362462261388169412⟩, ⟨498097461568353711, 498205979974193413⟩, true⟩

def words09 : List Nat := [371284109484940899, 371284109711256618, 371284111285330793, 371284112120625306, 371284113258326139, 371284114396193193, 371284115221346422, 371284115222060590, 371284113485171695, 371284112527641965]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 22790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 22700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 22700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk227
