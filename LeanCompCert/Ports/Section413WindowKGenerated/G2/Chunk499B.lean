import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk499A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk499B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk499A

def state06 : KState := ⟨⟨360550948857138591, 360550964514488053⟩, ⟨1545861287823064777, 1546389854885188159⟩, true⟩

def words05 : List Nat := [360581917699282383, 360581918207362968, 360581918515152347, 360581918515841742, 360581918423871927, 360581918141145181, 360581917974532467, 360581917975221921, 360581917692478701, 360581917073633073]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360612302441612833, 360612318105468199⟩, ⟨(-1519698830002358297), (-1519169937872868687)⟩, true⟩

def words06 : List Nat := [360581916454656283, 360581916107634476, 360581916158750289, 360581916253033936, 360581916253669644, 360581916003839383, 360581915965825798, 360581916056054959, 360581916465011604, 360581917074112556]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360563150458085366, 360563166128518295⟩, ⟨936699510601987905, 937228731443547849⟩, true⟩

def words07 : List Nat := [360581917483052639, 360581917892055538, 360581918044589095, 360581918398856254, 360581918645626893, 360581918892499546, 360581918934844051, 360581918935533744, 360581918578374206, 360581918203977350]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360540499565483951, 360540515242407772⟩, ⟨2068930726607266534, 2069460271896897204⟩, true⟩

def words08 : List Nat := [360581917829350940, 360581917760501009, 360581917423060094, 360581916885822268, 360581916348491454, 360581915589032498, 360581915028894236, 360581914343064334, 360581913657187816, 360581912727342697]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598043332315533, 360598059015749787⟩, ⟨(-807977783359174908), (-807447912580767286)⟩, true⟩

def words09 : List Nat := [360581911899801771, 360581911471699080, 360581911043411341, 360581911014471755, 360581910997150142, 360581910568005462, 360581910138746745, 360581909809364270, 360581910056783175, 360581910380470878]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk499B
