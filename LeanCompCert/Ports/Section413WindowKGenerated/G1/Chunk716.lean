import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk716

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362503340312663005, 362503416528706445⟩, ⟨(-1304321162828554308), (-1300635756701020546)⟩, true⟩

def state01 : KState := ⟨⟨362484397429176331, 362484473667407977⟩, ⟨52009542704009529, 55696537614831793⟩, true⟩

def words00 : List Nat := [371285251717671016, 371285251720126071, 371285251742689127, 371285251789090552, 371285251893267068, 371285251895722232, 371285251740181534, 371285251585797013, 371285251440512648, 371285251443383607]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 71600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 71600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362467379768244591, 362467456028530043⟩, ⟨1270801968828909121, 1274490543128508815⟩, true⟩

def words01 : List Nat := [371285251567201937, 371285251702851079, 371285251842158375, 371285251844614719, 371285251751436893, 371285251718561940, 371285251695323811, 371285251697779814, 371285251450794820, 371285251205060740]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 71610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 71600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478320531032763, 362478396813306347⟩, ⟨487150088477031124, 490840237676126434⟩, true⟩

def words02 : List Nat := [371285250958279634, 371285250756916956, 371285250476960782, 371285250365042638, 371285250252296674, 371285250114349012, 371285249741977101, 371285249520492295, 371285249297766374, 371285249252754569]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 71620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 71600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490577329143915, 362490653633872193⟩, ⟨(-390881226429573149), (-387189468690569225)⟩, true⟩

def words03 : List Nat := [371285249158979490, 371285249026876827, 371285248953602420, 371285248956309547, 371285248941768934, 371285248965795142, 371285248989358358, 371285248991866523, 371285248975994324, 371285249054529491]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 71630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 71600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478761039101570, 362478837365696045⟩, ⟨455712128574454514, 459405452923148200⟩, true⟩

def words04 : List Nat := [371285249294544859, 371285249300447114, 371285249302305260, 371285249270807913, 371285249238425653, 371285249187139475, 371285249080387151, 371285249126180437, 371285249162911159, 371285249165457708]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 71640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 71600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362496393756930817, 362496470105745872⟩, ⟨(-807715117804413366), (-804020201238189000)⟩, true⟩

def words05 : List Nat := [371285249163437851, 371285249252199681, 371285249513700653, 371285249601326618, 371285249641470449, 371285249682408547, 371285249895867544, 371285250014493136, 371285250172764869, 371285250332072072]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483107643341898, 362483184014322137⟩, ⟨144410515458905275, 148107020496985151⟩, true⟩

def words06 : List Nat := [371285250490873012, 371285250493330696, 371285250484666286, 371285250579723996, 371285250681742723, 371285250684243395, 371285250624247144, 371285250564881621, 371285250524989907, 371285250527793562]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472050539945494, 362472126933121552⟩, ⟨936988935519629873, 940687031440984473⟩, true⟩

def words07 : List Nat := [371285250666267900, 371285250834602382, 371285250962068496, 371285250964526676, 371285250832542974, 371285250737289172, 371285250716535698, 371285250718993941, 371285250537348582, 371285250357109289]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472304447041864, 362472380862200685⟩, ⟨918857424671834364, 922557096428374708⟩, true⟩

def words08 : List Nat := [371285250175696592, 371285250157933429, 371285250134872884, 371285250206361400, 371285250232998435, 371285250235457296, 371285250031525979, 371285249834370562, 371285249635926352, 371285249562109018]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484361285777189, 362484437723312480⟩, ⟨54441244348775396, 58142520390396170⟩, true⟩

def words09 : List Nat := [371285249384447526, 371285249193605260, 371285249002644647, 371285249005427118, 371285248936741332, 371285248907845862, 371285248878088875, 371285248849369706, 371285248645413779, 371285248637125457]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk716
