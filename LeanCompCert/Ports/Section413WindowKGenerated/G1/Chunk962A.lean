import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk962A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362499529965990873, 362499670725695534⟩, ⟨(-1393895359651018946), (-1384752980944218832)⟩, true⟩

def state01 : KState := ⟨⟨362487400416076130, 362487541206279831⟩, ⟨(-227006978914038680), (-217861666041617854)⟩, true⟩

def words00 : List Nat := [371285276485657066, 371285276489031441, 371285276553041241, 371285276621859906, 371285276716088066, 371285276719485393, 371285276717173222, 371285276715699002, 371285276763499232, 371285276790921488]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477460055463603, 362477600875978421⟩, ⟨729461953220618614, 738610182482718710⟩, true⟩

def words01 : List Nat := [371285276924911908, 371285277060244068, 371285277194372204, 371285277200570477, 371285277211784945, 371285277224667123, 371285277290850648, 371285277294225344, 371285277216614923, 371285277140606178]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487966508090441, 362488107358873558⟩, ⟨(-281454096610958226), (-272302954784936988)⟩, true⟩

def words02 : List Nat := [371285277091488771, 371285277095306862, 371285277205771436, 371285277317659436, 371285277410418437, 371285277413809781, 371285277472230611, 371285277545415724, 371285277645779423, 371285277678679183]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483344385416248, 362483485266977146⟩, ⟨163401491489460727, 172555595216961321⟩, true⟩

def words03 : List Nat := [371285277710175314, 371285277742847312, 371285277882235390, 371285277973967113, 371285278089187011, 371285278205727411, 371285278299818667, 371285278303194236, 371285278253065232, 371285278238664771]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481522598440991, 362481663510081376⟩, ⟨338728412354261007, 347885411087880803⟩, true⟩

def words04 : List Nat := [371285278301108630, 371285278304484305, 371285278241867649, 371285278159432418, 371285278075735460, 371285278025855382, 371285277920454083, 371285277915524153, 371285277909422206, 371285277903962809]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk962A
