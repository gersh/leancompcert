import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk793A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567349087862891, 360567390019417730⟩, ⟨1172449776430872414, 1174641993434042160⟩, true⟩

def state01 : KState := ⟨⟨360602237857686007, 360602278799950984⟩, ⟨(-1594460320276522063), (-1592267253906509941)⟩, true⟩

def words00 : List Nat := [360582202469022159, 360582202493709572, 360582202542243599, 360582202590979093, 360582202592027144, 360582202487142247, 360582202313400288, 360582202255984370, 360582202298258732, 360582202552596815]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 79300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 79300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590268041256761, 360590308994297283⟩, ⟨(-645079658536454347), (-642885737502649995)⟩, true⟩

def words01 : List Nat := [360582202727305819, 360582202902133978, 360582203124197481, 360582203426045713, 360582203652029382, 360582203878191480, 360582203981347302, 360582203982480719, 360582204029092314, 360582204132564544]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 79310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 79300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584370370182736, 360584411333901873⟩, ⟨(-177273337457764676), (-175078569344031112)⟩, true⟩

def words02 : List Nat := [360582204260298039, 360582204335880574, 360582204336890573, 360582204323327266, 360582204309562978, 360582204220649978, 360582204299502556, 360582204378569699, 360582204379580493, 360582204396269119]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 79320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 79300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591942980449235, 360591983954883541⟩, ⟨(-778080389233498039), (-775884771032855141)⟩, true⟩

def words03 : List Nat := [360582204420838116, 360582204445731396, 360582204628896409, 360582204653741352, 360582204654797624, 360582204529339041, 360582204435681468, 360582204591173299, 360582204715355629, 360582204839785007]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 79330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 79300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574625282653853, 360574666267877170⟩, ⟨595841345445871107, 598037819699450491⟩, true⟩

def words04 : List Nat := [360582204873667221, 360582204874800946, 360582204750080841, 360582204650355503, 360582204550333247, 360582204340975131, 360582204019633216, 360582203619036764, 360582203218233173, 360582202976379999]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 79340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 79300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk793A
