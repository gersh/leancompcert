import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk223A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk223B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk223A

def state06 : KState := ⟨⟨360522625382995592, 360522628313816917⟩, ⟨1287983027463749031, 1288027367211550751⟩, true⟩

def words05 : List Nat := [360580243094627639, 360580244510598421, 360580244913803151, 360580244914092410, 360580243325670381, 360580240502235070, 360580237678964453, 360580236293066201, 360580234976032793, 360580232400007058]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 22350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 22300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590733447270395, 360590736380820432⟩, ⟨(-235398525523090333), (-235354124747514465)⟩, true⟩

def words06 : List Nat := [360580229824145170, 360580228510173068, 360580228201591799, 360580227308608642, 360580226415689738, 360580223607009247, 360580219562261028, 360580217512969435, 360580215463776730, 360580215879960055]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 22360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 22300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360534781653824542, 360534784590135414⟩, ⟨1016684580295517693, 1016729042844415473⟩, true⟩

def words07 : List Nat := [360580215880218013, 360580215339294484, 360580214835722224, 360580216372653098, 360580217311061850, 360580218249433573, 360580218249691578, 360580218177709589, 360580216871982868, 360580214842273235]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 22370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 22300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563046494886405, 360563049433925574⟩, ⟨384054553182795874, 384099076804310688⟩, true⟩

def words08 : List Nat := [360580212812649642, 360580212775851264, 360580212407856876, 360580211014783762, 360580209621789723, 360580206650645857, 360580205549758673, 360580205659820876, 360580205660079675, 360580204372594816]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 22380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 22300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603046674334915, 360603049616112072⟩, ⟨(-511828145395579631), (-511783560456437171)⟩, true⟩

def words09 : List Nat := [360580204831528849, 360580206056594166, 360580207183124903, 360580207183414676, 360580206327131196, 360580203779148972, 360580201231337134, 360580201115171304, 360580202135429293, 360580203155665823]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 22390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 22300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 22300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk223B
