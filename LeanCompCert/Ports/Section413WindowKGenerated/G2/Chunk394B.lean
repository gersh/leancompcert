import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk394A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk394B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk394A

def state06 : KState := ⟨⟨360586026338787414, 360586035919358084⟩, ⟨(-142955890746655699), (-142700368325872899)⟩, true⟩

def words05 : List Nat := [360582408682800249, 360582411299685704, 360582413595101147, 360582415251395570, 360582416545429665, 360582417839542780, 360582418910930928, 360582419497015039, 360582419589146760, 360582419681342680]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360640191732039295, 360640201317651339⟩, ⟨(-2280575820816934075), (-2280320099438802129)⟩, true⟩

def words06 : List Nat := [360582420414411997, 360582421468404526, 360582422517388141, 360582423566419547, 360582424068246218, 360582424585417321, 360582425549047315, 360582426512792330, 360582427815719188, 360582429279966994]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360590303595776794, 360590313186482415⟩, ⟨(-311160855091482483), (-310904932645473871)⟩, true⟩

def words07 : List Nat := [360582430323278401, 360582431366595256, 360582432391027228, 360582433900950397, 360582435242666851, 360582436584402030, 360582437605091567, 360582437987660380, 360582438187568754, 360582438387651447]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575636271859087, 360575645867592869⟩, ⟨267896634155310209, 268152755139089535⟩, true⟩

def words08 : List Nat := [360582438775992615, 360582438889255118, 360582438889735794, 360582438590725021, 360582438291642434, 360582437705246283, 360582437438869345, 360582437154103578, 360582436869293894, 360582436264025867]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360641298525597757, 360641308126374966⟩, ⟨(-2325594967169598441), (-2325338646996287841)⟩, true⟩

def words09 : List Nat := [360582436092511991, 360582435789286783, 360582435640740029, 360582436134352984, 360582436134845855, 360582436079195489, 360582436450812837, 360582437302152537, 360582438792985528, 360582440283864744]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk394B
