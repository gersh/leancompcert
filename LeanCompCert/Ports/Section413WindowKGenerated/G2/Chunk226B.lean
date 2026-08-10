import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk226A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk226B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk226A

def state06 : KState := ⟨⟨360479679647430991, 360479682660954030⟩, ⟨2279663556902196574, 2279709758291995450⟩, true⟩

def words05 : List Nat := [360580301020675610, 360580301937824975, 360580301938088876, 360580301859975751, 360580300584884053, 360580298258848790, 360580295932933343, 360580294994606633, 360580292120831760, 360580287681178743]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 22650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 22600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360564346680310380, 360564349696600146⟩, ⟨360514682215718748, 360560946313752728⟩, true⟩

def words06 : List Nat := [360580283241850430, 360580278469214077, 360580274689664063, 360580272323990112, 360580269958502075, 360580265933664962, 360580261960359510, 360580258812498111, 360580255664828921, 360580254458237277]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 22660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 22600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561311188193385, 360561314207286338⟩, ⟨429014986895983561, 429061314555661885⟩, true⟩

def words07 : List Nat := [360580253756956456, 360580251521743255, 360580249286674124, 360580246335545017, 360580244356411799, 360580241850263586, 360580239344304504, 360580235861870734, 360580233088487689, 360580232254665336]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 22670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 22600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360545240945977730, 360545243967834353⟩, ⟨793611930076528399, 793658320430326427⟩, true⟩

def words08 : List Nat := [360580231652432541, 360580231652728116, 360580231612342098, 360580230596289658, 360580229580280134, 360580227444359490, 360580226463631708, 360580225402981912, 360580224342396054, 360580222298395408]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 22680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 22600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360672584952362144, 360672587976992092⟩, ⟨(-2096627971640900892), (-2096581518346623522)⟩, true⟩

def words09 : List Nat := [360580221152923701, 360580221549009845, 360580222218054132, 360580222935292085, 360580222935563735, 360580221763260100, 360580221354671586, 360580223488219183, 360580227557377257, 360580231626243376]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 22690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 22600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 22600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk226B
