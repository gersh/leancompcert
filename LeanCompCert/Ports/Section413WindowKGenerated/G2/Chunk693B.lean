import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk693A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk693B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk693A

def state06 : KState := ⟨⟨360558279413274683, 360558310396837483⟩, ⟨1691707701497109915, 1693159301131197277⟩, true⟩

def words05 : List Nat := [360582723479950379, 360582723250508681, 360582723020885812, 360582722990527431, 360582722991358436, 360582722839901944, 360582722688326046, 360582722410878946, 360582721925597691, 360582721574766134]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 69350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 69300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566905044006989, 360566936036828733⟩, ⟨1093337112354008999, 1094789354234183639⟩, true⟩

def words06 : List Nat := [360582721223615956, 360582721040989322, 360582720707854839, 360582720212432747, 360582719716865068, 360582719169483404, 360582718777815270, 360582718534946868, 360582718291973522, 360582717921710299]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 69360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 69300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360575894239014592, 360575925241095285⟩, ⟨469719369577752490, 471172253796426850⟩, true⟩

def words07 : List Nat := [360582717695004312, 360582717675888566, 360582717806565170, 360582717807546853, 360582717750964103, 360582717499605830, 360582717248088679, 360582716824969303, 360582716520636453, 360582716423767474]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 69370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 69300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360569605021603378, 360569636033043107⟩, ⟨905966181592960429, 907419715186499481⟩, true⟩

def words08 : List Nat := [360582716326772246, 360582716093739611, 360582715699776385, 360582715513346606, 360582715326642882, 360582715088064076, 360582714641872245, 360582714068650654, 360582713495248836, 360582713129385325]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 69380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 69300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554434597582244, 360554465618282324⟩, ⟨1958712969711295560, 1960167145927550682⟩, true⟩

def words09 : List Nat := [360582712941739117, 360582712682359449, 360582712422880327, 360582712059887353, 360582711744307877, 360582711376992910, 360582711009401256, 360582710755499871, 360582710507622192, 360582710101653038]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 69390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 69300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 69300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk693B
