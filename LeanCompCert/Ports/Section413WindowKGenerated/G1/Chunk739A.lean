import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk739A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468099837410894, 362468181229191372⟩, ⟨1260044745276408332, 1264106720333203062⟩, true⟩

def state01 : KState := ⟨⟨362487909318730504, 362487990733243524⟩, ⟨(-203932999078494498), (-199869343969979168)⟩, true⟩

def words00 : List Nat := [371285286638423501, 371285286567507976, 371285286437529295, 371285286458695991, 371285286460884598, 371285286463469430, 371285286343796973, 371285286377545082, 371285286504603660, 371285286543826929]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 73900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 73900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490160242604641, 362490241680335562⟩, ⟨(-370321293593829521), (-366255922342374167)⟩, true⟩

def words01 : List Nat := [371285286570727742, 371285286598508653, 371285286701812676, 371285286722778461, 371285286798694135, 371285286875565873, 371285286948674113, 371285286951227300, 371285286916217243, 371285286986509148]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 73910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 73900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476642595565140, 362476724055887302⟩, ⟨629006937177626710, 633073978493558786⟩, true⟩

def words02 : List Nat := [371285287191937932, 371285287201375636, 371285287203275906, 371285287192815617, 371285287224752864, 371285287227583634, 371285287194029593, 371285287204584366, 371285287207300836, 371285287209931582]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 73920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 73900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362494721131648487, 362494802614902571⟩, ⟨(-707671098811127548), (-703602362019954652)⟩, true⟩

def words03 : List Nat := [371285287095849579, 371285287026006843, 371285286998325218, 371285287000911097, 371285286894136005, 371285286767389571, 371285286677210641, 371285286680011473, 371285286756485169, 371285286888011943]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 73930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 73900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486819530853939, 362486901037089007⟩, ⟨(-123427495225511198), (-119357059109472984)⟩, true⟩

def words04 : List Nat := [371285286984386412, 371285286986945481, 371285287031905931, 371285287147947581, 371285287285853306, 371285287288395224, 371285287182773207, 371285287072120529, 371285287010387683, 371285287035126769]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 73940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 73900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk739A
