import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk513A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk513B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk513A

def state06 : KState := ⟨⟨360543334334396477, 360543350918946372⟩, ⟨1980878207612391218, 1981453749858137656⟩, true⟩

def words05 : List Nat := [360581931084089817, 360581930958282331, 360581930986224066, 360581931334559673, 360581931588245046, 360581931842036820, 360581931842672577, 360581931798722678, 360581931376281222, 360581930625914015]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360562104559588034, 360562121150823401⟩, ⟨1016696932111945721, 1017272817757949273⟩, true⟩

def words06 : List Nat := [360581929875340400, 360581929503073226, 360581928878906299, 360581928012291785, 360581927145595154, 360581926184808855, 360581925515807763, 360581925076664546, 360581924637460861, 360581924008868135]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585241509226660, 360585258107174741⟩, ⟨(-172050798768251360), (-171474568257162766)⟩, true⟩

def words07 : List Nat := [360581923623955578, 360581923496968904, 360581923369781841, 360581923115225420, 360581922736883184, 360581922025461247, 360581921313926118, 360581920892127711, 360581920726740786, 360581920792442503]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360552554042125880, 360552570646842720⟩, ⟨1507518687527101683, 1508095265850435213⟩, true⟩

def words08 : List Nat := [360581920793086205, 360581920567845877, 360581920167365029, 360581920144871508, 360581920122190929, 360581919928061931, 360581919355949338, 360581918493666953, 360581917631284352, 360581916731019612]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360531420780475669, 360531437391882014⟩, ⟨2593708153595101633, 2594285075726185073⟩, true⟩

def words09 : List Nat := [360581916160560297, 360581915718919728, 360581915277214233, 360581914594616776, 360581913922904748, 360581913065221914, 360581912207364121, 360581911636821143, 360581910845409601, 360581909864172407]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk513B
