import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk877

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483659532267909, 362483775683313085⟩, ⟨115905058712661472, 122782931306638212⟩, true⟩

def state01 : KState := ⟨⟨362487742204084194, 362487858382464467⟩, ⟨(-242163829110630058), (-235283559087601090)⟩, true⟩

def words00 : List Nat := [371285175816785089, 371285175879068850, 371285175923759655, 371285175969670644, 371285175993101401, 371285175996155386, 371285175846046271, 371285175813240767, 371285175862326157, 371285175896127661]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 87700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 87700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492102177883659, 362492218384111567⟩, ⟨(-624585769969185905), (-617703057292760181)⟩, true⟩

def words01 : List Nat := [371285175927607713, 371285175960150933, 371285176108852412, 371285176213392982, 371285176345491098, 371285176478728330, 371285176585936349, 371285176588991188, 371285176621768271, 371285176705866988]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 87710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 87700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487618430321408, 362487734663757295⟩, ⟨(-231225764490799380), (-224340664989891616)⟩, true⟩

def words02 : List Nat := [371285176918053435, 371285176990839857, 371285177059105350, 371285177128418020, 371285177191281629, 371285177194647892, 371285177289430360, 371285177389714035, 371285177488986469, 371285177521299215]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 87720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 87700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495475695623012, 362495591956669557⟩, ⟨(-920608424769978430), (-913720902843693940)⟩, true⟩

def words03 : List Nat := [371285177597007518, 371285177674263151, 371285177855591796, 371285177864787631, 371285177867151505, 371285177855779634, 371285177879574275, 371285177882999724, 371285177992666334, 371285178114761627]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 87730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 87700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485999176259214, 362486115464891660⟩, ⟨(-89115355904378137), (-82225413456007837)⟩, true⟩

def words04 : List Nat := [371285178236146142, 371285178239207963, 371285178340223010, 371285178458285928, 371285178567315189, 371285178570370963, 371285178525161220, 371285178454972048, 371285178419599765, 371285178433821291]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 87740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 87700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490563488743928, 362490679804941117⟩, ⟨(-489605622504223038), (-482713261109042914)⟩, true⟩

def words05 : List Nat := [371285178576332560, 371285178720170298, 371285178862937142, 371285178906300141, 371285178988542888, 371285179072263264, 371285179272619129, 371285179357442959, 371285179422465452, 371285179488614856]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495076844561258, 362495193188102852⟩, ⟨(-885701870889248011), (-878807109611192867)⟩, true⟩

def words06 : List Nat := [371285179625875927, 371285179699560693, 371285179837867331, 371285179977378496, 371285180095135612, 371285180105804249, 371285180245155266, 371285180386156706, 371285180571179328, 371285180688420598]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490372922985641, 362490489294399789⟩, ⟨(-472811797987467603), (-465914590200798477)⟩, true⟩

def words07 : List Nat := [371285180789220421, 371285180891016719, 371285181045429065, 371285181136265918, 371285181264296143, 371285181393551572, 371285181520199222, 371285181523255788, 371285181537184489, 371285181601502684]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476767246588317, 362476883645181129⟩, ⟨721580824201034391, 728480417876229101⟩, true⟩

def words08 : List Nat := [371285181763026003, 371285181766083039, 371285181754887166, 371285181734222881, 371285181713909073, 371285181717309834, 371285181655989143, 371285181649665623, 371285181642338808, 371285181633766119]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494074586079203, 362494191012317755⟩, ⟨(-797932588645231149), (-791030567811460043)⟩, true⟩

def words09 : List Nat := [371285181541336501, 371285181486952004, 371285181502497593, 371285181505608370, 371285181471773550, 371285181417411197, 371285181433819413, 371285181444387821, 371285181549080082, 371285181655159962]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk877
