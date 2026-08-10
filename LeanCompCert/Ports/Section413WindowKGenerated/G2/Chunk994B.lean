import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk994A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk994B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk994A

def state06 : KState := ⟨⟨360580635887640304, 360580701417417539⟩, ⟨168291834893542817, 172692673357589713⟩, true⟩

def words05 : List Nat := [360582436983319208, 360582437209219641, 360582437384344024, 360582437458821103, 360582437507499669, 360582437556589606, 360582437689347779, 360582437734845711, 360582437736146439, 360582437720186065]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599151268299035, 360599216811751183⟩, ⟨(-1673377442781521043), (-1668975244145375135)⟩, true⟩

def words06 : List Nat := [360582437762613412, 360582437902233256, 360582438000282169, 360582438098580348, 360582438111170219, 360582438112617119, 360582438066117680, 360582438054690249, 360582438130783449, 360582438300987791]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583766895102211, 360583832452317108⟩, ⟨(-143010446256481489), (-138606878570975055)⟩, true⟩

def words07 : List Nat := [360582438413972254, 360582438527112306, 360582438655594196, 360582438845562514, 360582438978543495, 360582439111761677, 360582439166934082, 360582439168380491, 360582439136648335, 360582439152304332]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582992297080105, 360583057867915761⟩, ⟨(-65975144705805598), (-61570221958459778)⟩, true⟩

def words08 : List Nat := [360582439237914813, 360582439239361267, 360582439224336932, 360582439158953691, 360582439093293247, 360582438988310739, 360582438978872328, 360582439025495059, 360582439026789775, 360582439015738595]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586186016405543, 360586251600910074⟩, ⟨(-383794288030073650), (-379388005301123034)⟩, true⟩

def words09 : List Nat := [360582439016928491, 360582439001437613, 360582439027247432, 360582439028694095, 360582438971046616, 360582438810844690, 360582438650368589, 360582438615141279, 360582438654633573, 360582438694453847]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk994B
