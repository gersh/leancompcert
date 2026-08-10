import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk782A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk782B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk782A

def state06 : KState := ⟨⟨362503127289374620, 362503218974147391⟩, ⟨(-1411754049317821513), (-1406908752454862613)⟩, true⟩

def words05 : List Nat := [371285240788947247, 371285240912675401, 371285241102271658, 371285241146024833, 371285241149010471, 371285241152851617, 371285241302862591, 371285241372381592, 371285241603929608, 371285241836716808]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 78250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 78200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481657187497117, 362481748896609530⟩, ⟨268588317700381909, 273435519510643113⟩, true⟩

def words06 : List Nat := [371285242061737034, 371285242089690318, 371285242255124062, 371285242422008202, 371285242591593272, 371285242594294231, 371285242546511041, 371285242467654887, 371285242387721758, 371285242387340470]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 78260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 78200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476660548978447, 362476752282438809⟩, ⟨659754542273713722, 664603649922062600⟩, true⟩

def words07 : List Nat := [371285242421914438, 371285242502256219, 371285242570418305, 371285242573166672, 371285242505466166, 371285242470243436, 371285242558292275, 371285242560993728, 371285242470226924, 371285242364834339]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 78270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 78200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481369538350128, 362481461296032570⟩, ⟨291126832035552302, 295977835912521934⟩, true⟩

def words08 : List Nat := [371285242258242642, 371285242205327950, 371285242096227399, 371285242125215591, 371285242127312067, 371285242113668896, 371285241943149890, 371285241856861721, 371285241825052007, 371285241827849054]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 78280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 78200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480316198697698, 362480407980973336⟩, ⟨373621326816420756, 378474256217659070⟩, true⟩

def words09 : List Nat := [371285241781599554, 371285241735624293, 371285241773302626, 371285241779479944, 371285241790942380, 371285241803430479, 371285241814911622, 371285241817632024, 371285241682467415, 371285241624092336]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 78290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 78200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 78200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk782B
