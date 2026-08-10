import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk888A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk888B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk888A

def state06 : KState := ⟨⟨360585678676773865, 360585730527989231⟩, ⟨(-327785148842964428), (-324673744506303208)⟩, true⟩

def words05 : List Nat := [360582077031967615, 360582076890714502, 360582076749218988, 360582076797695188, 360582076798772174, 360582076793114936, 360582076787328912, 360582076718970186, 360582076759427838, 360582076802007009]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584725431345369, 360584777294615731⟩, ⟨(-243079839311394918), (-239967363705463298)⟩, true⟩

def words06 : List Nat := [360582076970586615, 360582077039350061, 360582077040493783, 360582077032583243, 360582077024482573, 360582076929539111, 360582076992099227, 360582077087355579, 360582077088504692, 360582077118363574]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596512222652477, 360596564098031475⟩, ⟨(-1290597139700279864), (-1287483587941358886)⟩, true⟩

def words07 : List Nat := [360582077256989049, 360582077396014406, 360582077661035820, 360582077854293862, 360582077938617093, 360582078023028822, 360582078126427704, 360582078293732508, 360582078457767797, 360582078622081145]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602768513971831, 360602820401543982⟩, ⟨(-1846784461584515634), (-1843669826037307188)⟩, true⟩

def words08 : List Nat := [360582078695855122, 360582078715211354, 360582078860693649, 360582079006563678, 360582079093612874, 360582079186895225, 360582079216609852, 360582079246464137, 360582079373801941, 360582079608594895]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580480147388417, 360580532047045697⟩, ⟨134557336026500026, 137673045880953476⟩, true⟩

def words09 : List Nat := [360582079862347249, 360582080116332672, 360582080260509752, 360582080375064407, 360582080422137265, 360582080469547516, 360582080642915111, 360582080690160173, 360582080691301989, 360582080675233335]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk888B
