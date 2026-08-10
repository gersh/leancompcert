import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk940A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk940B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk940A

def state06 : KState := ⟨⟨362483445816183313, 362483580149267234⟩, ⟨139889966791878050, 148420953094759224⟩, true⟩

def words05 : List Nat := [371285157631666406, 371285157745591806, 371285157858404268, 371285157872923201, 371285157906944931, 371285157942614663, 371285158089625599, 371285158098960103, 371285158101487959, 371285158088381574]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 94050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 94000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362493538361015408, 362493672723589033⟩, ⟨(-809465944842460777), (-800932184589564017)⟩, true⟩

def words06 : List Nat := [371285158085400772, 371285158089031619, 371285158122707850, 371285158198581937, 371285158255757351, 371285158259108864, 371285158286825141, 371285158355631445, 371285158505391246, 371285158599314926]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 94060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 94000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493397650555214, 362493532043215711⟩, ⟨(-796240401755540607), (-787703811087513035)⟩, true⟩

def words07 : List Nat := [371285158692034168, 371285158785918854, 371285158912282693, 371285158983613314, 371285159077303762, 371285159172224922, 371285159266441340, 371285159269744794, 371285159336935897, 371285159430136689]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 94070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 94000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479517647602489, 362479652069566263⟩, ⟨509667966686653373, 518207314362324371⟩, true⟩

def words08 : List Nat := [371285159596088499, 371285159612506782, 371285159614985479, 371285159611551526, 371285159627879129, 371285159631544277, 371285159609581885, 371285159624512812, 371285159636719015, 371285159640130216]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 94080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 94000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362503539226900911, 362503673678615727⟩, ⟨(-1750645876903296277), (-1742103729800091823)⟩, true⟩

def words09 : List Nat := [371285159613179961, 371285159646436434, 371285159759294857, 371285159838853465, 371285159880331796, 371285159922844920, 371285160065193432, 371285160152585774, 371285160351562839, 371285160551977327]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 94090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 94000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 94000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk940B
