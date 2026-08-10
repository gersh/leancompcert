import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk575A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502345649552738, 362502393962478851⟩, ⟨(-1002860766797073584), (-1000984202513385346)⟩, true⟩

def state01 : KState := ⟨⟨362484730089080555, 362484778419506625⟩, ⟨10069197690306152, 11946768310399934⟩, true⟩

def words00 : List Nat := [371284986150224974, 371284986152164626, 371284986258565276, 371284986464771753, 371284986678455399, 371284986680395186, 371284986490973852, 371284986286946871, 371284986151027255, 371284986153262675]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 57500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 57500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362466921020930647, 362466969368863203⟩, ⟨1034436168489448556, 1036314745997150484⟩, true⟩

def words01 : List Nat := [371284986339856708, 371284986530905495, 371284986710597802, 371284986712537876, 371284986519775759, 371284986419292597, 371284986497885792, 371284986499825927, 371284986278391820, 371284985967368022]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 57510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 57500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491090447319022, 362491138812620972⟩, ⟨(-355921792228908602), (-354042215546704988)⟩, true⟩

def words02 : List Nat := [371284985655466790, 371284985588968470, 371284985371469916, 371284985287614030, 371284985203184142, 371284985072846287, 371284984693686638, 371284984617966754, 371284984765482594, 371284984874473770]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 57520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 57500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490868979390881, 362490917362371559⟩, ⟨(-343188234193359785), (-341307640366073297)⟩, true⟩

def words03 : List Nat := [371284984966935608, 371284985060035602, 371284985276281563, 371284985357702445, 371284985490413149, 371284985623892212, 371284985754292048, 371284985756242114, 371284985701270268, 371284985806778746]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 57530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 57500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362467227652834704, 362467276053077589⟩, ⟨1017265023538138277, 1019146610724423675⟩, true⟩

def words04 : List Nat := [371284986065557833, 371284986067498951, 371284985923741790, 371284985779288664, 371284985634084464, 371284985521487223, 371284985283846263, 371284985170891766, 371284985057304029, 371284984942925103]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 57540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 57500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk575A
