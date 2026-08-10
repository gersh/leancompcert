import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk637A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488481409412668, 362488541185546409⟩, ⟨(-201537323572852626), (-198965436918594632)⟩, true⟩

def state01 : KState := ⟨⟨362496067952256231, 362496127747736641⟩, ⟨(-684813854042012209), (-682240734903321245)⟩, true⟩

def words00 : List Nat := [371285417934586169, 371285417988205670, 371285418287492650, 371285418587670064, 371285418853678772, 371285418855844581, 371285418874075087, 371285418919780156, 371285419210961973, 371285419381286526]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 63700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 63700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496885213316114, 362496945028578805⟩, ⟨(-736874940346765229), (-734300560783878177)⟩, true⟩

def words01 : List Nat := [371285419552013109, 371285419723496562, 371285420011338205, 371285420218037489, 371285420498400416, 371285420779570415, 371285421043842345, 371285421046008300, 371285421162684724, 371285421346263966]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 63710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 63700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486699336184286, 362486759170765830⟩, ⟨(-87791777139666419), (-85216166479457805)⟩, true⟩

def words02 : List Nat := [371285421630204136, 371285421632370265, 371285421615405529, 371285421552531216, 371285421498149519, 371285421500554089, 371285421647147306, 371285421845350607, 371285422024847207, 371285422048070761]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 63720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 63700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362505396512058447, 362505456366186505⟩, ⟨(-1279456138803258736), (-1276879282342531294)⟩, true⟩

def words03 : List Nat := [371285422280179328, 371285422513380402, 371285422830373586, 371285422927700972, 371285422959831250, 371285422992626764, 371285423270906252, 371285423426693780, 371285423742462382, 371285424059157395]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 63730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 63700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492183911138918, 362492243784840153⟩, ⟨(-437207303698524317), (-434629199546312867)⟩, true⟩

def words04 : List Nat := [371285424374205339, 371285424529620175, 371285424930624904, 371285425332772346, 371285425722906620, 371285425785652765, 371285425846450743, 371285425907941679, 371285426069424601, 371285426178848933]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 63740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 63700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk637A
