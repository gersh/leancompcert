import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk877A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk877A
