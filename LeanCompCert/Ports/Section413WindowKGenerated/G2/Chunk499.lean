import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk499

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581459627059223, 360581475245288048⟩, ⟨21344402336480889, 21871016107131769⟩, true⟩

def state01 : KState := ⟨⟨360591418718429062, 360591434343162977⟩, ⟨(-475668973732502227), (-475142035325375137)⟩, true⟩

def words00 : List Nat := [360581913840954899, 360581914350776478, 360581914851584495, 360581915352494653, 360581915516120852, 360581915516809419, 360581915279890668, 360581914902926576, 360581914525776347, 360581914557237523]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 49900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 49900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584566798840346, 360584582430131997⟩, ⟨(-133731573387041975), (-133204307650185931)⟩, true⟩

def words01 : List Nat := [360581914557851014, 360581914515332907, 360581914472684385, 360581914609345766, 360581914631638424, 360581914654042461, 360581914654666641, 360581914366640728, 360581914073821120, 360581914128061723]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 49910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 49900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591540364137170, 360591556001910708⟩, ⟨(-481879909095852957), (-481352319750299393)⟩, true⟩

def words02 : List Nat := [360581914582322305, 360581914738602509, 360581914739222635, 360581914661167785, 360581914582992503, 360581914453011952, 360581914909891462, 360581915366884671, 360581915458042138, 360581915651832595]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 49920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 49900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360608670239306904, 360608685883594997⟩, ⟨(-1337466432799871834), (-1336938518151495174)⟩, true⟩

def words03 : List Nat := [360581915828482391, 360581916005325959, 360581916113824915, 360581916114513998, 360581915823125478, 360581915186979714, 360581914550727526, 360581914450810207, 360581914987439347, 360581915524207891]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 49930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 49900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612641765642268, 360612657416493011⟩, ⟨(-1536033230012198044), (-1535504987593725976)⟩, true⟩

def words04 : List Nat := [360581915834406899, 360581915835096094, 360581916055085868, 360581916365540643, 360581916393522064, 360581916507562016, 360581916508175963, 360581916421924889, 360581916575105383, 360581917191320468]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 49940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 49900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk499
