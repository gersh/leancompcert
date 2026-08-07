import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk517

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477362628116522, 362477401354325562⟩, ⟨392581517763559814, 393934117755776306⟩, true⟩

def state01 : KState := ⟨⟨362475643363331667, 362475682105026006⟩, ⟨481546174152037551, 482899574813882887⟩, true⟩

def words00 : List Nat := [371285020823557761, 371285020815912816, 371285020843255283, 371285021017624751, 371285021128442571, 371285021130172822, 371285020785183666, 371285020720792766, 371285020714235078, 371285020716026082]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 51700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 51700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490379278891666, 362490418036374649⟩, ⟨(-280522301977524648), (-279168084805519112)⟩, true⟩

def words01 : List Nat := [371285020536736487, 371285020285280200, 371285020153203391, 371285020157026897, 371285020275765526, 371285020395177888, 371285020514483222, 371285020516217514, 371285020352762437, 371285020459282066]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 51710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 51700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483761701412796, 362483800474329931⟩, ⟨61825913197819189, 63180928704364521⟩, true⟩

def words02 : List Nat := [371285020938149880, 371285021082990511, 371285021150161781, 371285021217863817, 371285021394643910, 371285021396551941, 371285021545855564, 371285021697894841, 371285021832041371, 371285021833864135]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 51720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 51700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487759818219281, 362487798606754775⟩, ⟨(-145024085071641213), (-143668261547351029)⟩, true⟩

def words03 : List Nat := [371285022008434534, 371285022207501914, 371285022597413453, 371285022599144601, 371285022491534450, 371285022320989627, 371285022149754361, 371285022076677221, 371285021869959821, 371285021925562929]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 51730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 51700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473757218896885, 362473796023079258⟩, ⟨579476078268279517, 580832711436256781⟩, true⟩

def words04 : List Nat := [371285021979549116, 371285021981281325, 371285021603646566, 371285021529535289, 371285021467268042, 371285021468999638, 371285020985630097, 371285020480796768, 371285019975290156, 371285019843590104]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 51740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 51700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362459633053340644, 362459671873142374⟩, ⟨1310495518191263212, 1311852959741441194⟩, true⟩

def words05 : List Nat := [371285019627904534, 371285019567295168, 371285019506095429, 371285019440476871, 371285018926896535, 371285018425562644, 371285017923366466, 371285017756164718, 371285017278924399, 371285016791220841]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 51750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 51700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492136399942296, 362492175235242376⟩, ⟨(-372024562184661859), (-370666318360362589)⟩, true⟩

def words06 : List Nat := [371285016302743523, 371285016156962507, 371285015824108736, 371285015776997203, 371285015729393025, 371285015536728826, 371285015121482747, 371285015079892834, 371285015366374790, 371285015506468345]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 51760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 51700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475638743293770, 362475677594376864⟩, ⟨482226031165055372, 483585092157070270⟩, true⟩

def words07 : List Nat := [371285015646354286, 371285015786836258, 371285016190761780, 371285016409134234, 371285016715890730, 371285017023318390, 371285017258284292, 371285017260017110, 371285016998036360, 371285016819795116]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 51770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 51700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475455707085026, 362475494573598019⟩, ⟨491739867363329691, 493099727395598973⟩, true⟩

def words08 : List Nat := [371285016775804562, 371285016777542303, 371285016532842374, 371285016252676081, 371285015971842813, 371285015806984126, 371285015579799496, 371285015653709584, 371285015709618216, 371285015711412184]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 51780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 51700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496973450920948, 362497012333149110⟩, ⟨(-622736888280606936), (-621376214284330898)⟩, true⟩

def words09 : List Nat := [371285015660208370, 371285015793767064, 371285016060940486, 371285016063122962, 371285016064477226, 371285016010577825, 371285016272513689, 371285016418567956, 371285016651337006, 371285016884909032]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 51790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 51700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 51700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk517
