import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk675A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk675B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk675A

def state06 : KState := ⟨⟨360563591578607925, 360563620913497404⟩, ⟨1300304857493159641, 1301643581951162965⟩, true⟩

def words05 : List Nat := [360582890399756479, 360582889986521582, 360582889573116634, 360582889299787433, 360582889140552137, 360582888878335849, 360582888616038165, 360582888183650109, 360582887680448421, 360582887396356362]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 67550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 67500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580258365732009, 360580287709603195⟩, ⟨174190595874440756, 175529927180991960⟩, true⟩

def words06 : List Nat := [360582887111959810, 360582886892293429, 360582886724231397, 360582886445807619, 360582886167217873, 360582885833825364, 360582885610320883, 360582885605727512, 360582885601029908, 360582885459006496]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 67560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 67500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360610422388266739, 360610451741160515⟩, ⟨(-1864263518244646068), (-1862923577237825612)⟩, true⟩

def words07 : List Nat := [360582885421346953, 360582885369749531, 360582885317869217, 360582885314542010, 360582885315425653, 360582885119235024, 360582884944396262, 360582885134726765, 360582885543409019, 360582885952296222]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 67570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 67500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592760112835865, 360592789474821220⟩, ⟨(-670714122871017430), (-669373567408703268)⟩, true⟩

def words08 : List Nat := [360582886251102619, 360582886331295916, 360582886507248227, 360582886683480679, 360582886708091269, 360582886709045940, 360582886588523358, 360582886330809418, 360582886072920209, 360582886180486047]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 67580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 67500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360555287026028821, 360555316397016958⟩, ⟨1862370077008159565, 1863711241012276207⟩, true⟩

def words09 : List Nat := [360582886504363213, 360582886828432893, 360582887042906096, 360582887043860562, 360582887039659075, 360582886892210230, 360582886744486491, 360582886700404666, 360582886496779160, 360582886089931341]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 67590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 67500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 67500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk675B
