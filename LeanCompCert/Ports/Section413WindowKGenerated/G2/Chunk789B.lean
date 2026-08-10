import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk789A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk789B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk789A

def state06 : KState := ⟨⟨360583071125776762, 360583111693581054⟩, ⟨(-73626320666316701), (-71462887276418091)⟩, true⟩

def words05 : List Nat := [360582206989387397, 360582206933468502, 360582206877350727, 360582206836833947, 360582206837777947, 360582206818194334, 360582206798498498, 360582206691064064, 360582206640507730, 360582206653279179]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 78950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 78900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577297605386160, 360577338183810143⟩, ⟨382311929321908067, 384476201296236199⟩, true⟩

def words06 : List Nat := [360582206814023798, 360582206927871679, 360582206961417874, 360582206995088655, 360582206996035304, 360582206973905774, 360582206974834495, 360582206963661201, 360582206952372046, 360582206820017516]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 78960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 78900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360618784564631728, 360618825153700327⟩, ⟨(-2894154886656452493), (-2891989774023960033)⟩, true⟩

def words07 : List Nat := [360582206826978873, 360582206895920597, 360582207092735248, 360582207294405009, 360582207358813686, 360582207423291338, 360582207647629479, 360582207952432536, 360582208416970888, 360582208881761203]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 78970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 78900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360621818948500602, 360621859548326775⟩, ⟨(-3133928691088557521), (-3131762728769941413)⟩, true⟩

def words08 : List Nat := [360582209223187010, 360582209597684962, 360582210043073961, 360582210488792596, 360582210894274898, 360582211185276279, 360582211390882275, 360582211596632393, 360582211962170983, 360582212465383530]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 78980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 78900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580647841941389, 360580688452384381⟩, ⟨118399801892168493, 120566602885401081⟩, true⟩

def words09 : List Nat := [360582212941063121, 360582213416940345, 360582213791867097, 360582214046009706, 360582214164026018, 360582214282322524, 360582214535546562, 360582214629055023, 360582214630063365, 360582214611914576]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 78990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 78900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 78900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk789B
