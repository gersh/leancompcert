import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk688

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474061532294233, 362474131685540848⟩, ⟨774121100955776045, 777380837635295273⟩, true⟩

def state01 : KState := ⟨⟨362476770478197817, 362476840652504587⟩, ⟨587767740528873395, 591028926255281589⟩, true⟩

def words00 : List Nat := [371285430689344934, 371285430691937026, 371285430623838074, 371285430635937290, 371285430637787070, 371285430587538588, 371285430255184936, 371285430115413326, 371285429974412206, 371285429940780351]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 68800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 68800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484746175312766, 362484816371024206⟩, ⟨38934051650429952, 42196710338474372⟩, true⟩

def words01 : List Nat := [371285429817714573, 371285429695725180, 371285429659133702, 371285429661750513, 371285429689925765, 371285429738072573, 371285429739863665, 371285429741208998, 371285429523080067, 371285429517062255]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 68810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 68800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480807919593321, 362480878136243976⟩, ⟨310037998215936807, 313302098052575945⟩, true⟩

def words02 : List Nat := [371285429711642770, 371285429714355460, 371285429716186449, 371285429718860038, 371285429785541542, 371285429788134646, 371285429817442757, 371285429888232597, 371285429958565150, 371285429961001387]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 68820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 68800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490376316474338, 362490446554465829⟩, ⟨(-348614702997698255), (-345349134164842831)⟩, true⟩

def words03 : List Nat := [371285429919240261, 371285429944862002, 371285430103493553, 371285430105847310, 371285430009064325, 371285429890513662, 371285429805455882, 371285429808112677, 371285429858973474, 371285429934513115]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 68830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 68800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471836534766725, 362471906794005070⟩, ⟨927725234412625458, 930992265985914910⟩, true⟩

def words04 : List Nat := [371285430008729425, 371285430011083578, 371285429804077201, 371285429773814368, 371285429742443407, 371285429725716109, 371285429479811339, 371285429230136566, 371285428979478622, 371285428831274292]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 68840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 68800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362458073719950298, 362458144000377769⟩, ⟨1875436624146174447, 1878705114699697051⟩, true⟩

def words05 : List Nat := [371285428636476613, 371285428617611193, 371285428597928607, 371285428561545742, 371285428268020858, 371285428030328857, 371285427791397120, 371285427716952798, 371285427361054821, 371285426967480582]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475469775496454, 362475540076987415⟩, ⟨677488810614658772, 680758751708905928⟩, true⟩

def words06 : List Nat := [371285426572881717, 371285426318852090, 371285425976378835, 371285425845438905, 371285425713735287, 371285425548787767, 371285425207226857, 371285425001147985, 371285424793854258, 371285424769185890]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470712824596680, 362470783147600110⟩, ⟨1005117656671060063, 1008389079434547633⟩, true⟩

def words07 : List Nat := [371285424627433342, 371285424444929825, 371285424261480098, 371285424167826077, 371285423993327315, 371285423853744240, 371285423713408687, 371285423573520430, 371285423152138551, 371285422942597708]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362464912515196337, 362464982859161808⟩, ⟨1404739147624204199, 1408012014361454491⟩, true⟩

def words08 : List Nat := [371285422731657720, 371285422731917269, 371285422579964979, 371285422429114055, 371285422277381904, 371285422148396753, 371285421926655054, 371285421755840306, 371285421584213362, 371285421413587145]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497707591921113, 362497777957152413⟩, ⟨(-854679924550078066), (-851405592701906644)⟩, true⟩

def words09 : List Nat := [371285421118505284, 371285421034987070, 371285420972574600, 371285420974978774, 371285420874815334, 371285420741485245, 371285420681578156, 371285420684174110, 371285420834153235, 371285421016139919]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk688
