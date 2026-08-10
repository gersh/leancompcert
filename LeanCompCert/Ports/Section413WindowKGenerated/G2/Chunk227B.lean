import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk227A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk227B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk227A

def state06 : KState := ⟨⟨360663672466323161, 360663675507671573⟩, ⟨(-1897559989118144830), (-1897513155813851054)⟩, true⟩

def words05 : List Nat := [360580276413550400, 360580280623290707, 360580286113796235, 360580290530741746, 360580293019640069, 360580295508342469, 360580297930818510, 360580301318637507, 360580304982067092, 360580308645239613]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 22750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 22700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360613883332053354, 360613886376214361⟩, ⟨(-764591606864763194), (-764544709532507184)⟩, true⟩

def words06 : List Nat := [360580311328712312, 360580313245180143, 360580314634843955, 360580316024475399, 360580316453445178, 360580316453740194, 360580314967149445, 360580312514473302, 360580310061956415, 360580311008003369]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 22760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 22700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360574826973036334, 360574830019977916⟩, ⟨124838971948173409, 124885932608244781⟩, true⟩

def words07 : List Nat := [360580312417823054, 360580313827571087, 360580314271916231, 360580314272211388, 360580313559413257, 360580312327403597, 360580311785539670, 360580312522264592, 360580312522530004, 360580312282164407]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 22770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 22700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360624628033999632, 360624631083726473⟩, ⟨(-1009980502936838935), (-1009933478814790529)⟩, true⟩

def words08 : List Nat := [360580312041754761, 360580311451073272, 360580313558637566, 360580315666073145, 360580316060803638, 360580316061098829, 360580314948079283, 360580315352330347, 360580316319102520, 360580318263805681]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 22780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 22700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360547351516151654, 360547354568694220⟩, ⟨751700827314210014, 751747915620455240⟩, true⟩

def words09 : List Nat := [360580319049607091, 360580319835378815, 360580321483303791, 360580324381752246, 360580326324212026, 360580328266549473, 360580328795569975, 360580328795865358, 360580327414342112, 360580325968502135]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 22790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 22700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 22700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk227B
