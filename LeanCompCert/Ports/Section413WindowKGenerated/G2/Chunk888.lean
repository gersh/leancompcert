import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk888

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360556790605867347, 360556842384351272⟩, ⟨2237880113190218313, 2240985056797193197⟩, true⟩

def state01 : KState := ⟨⟨360570202630340196, 360570254420898766⟩, ⟨1046832631130256926, 1049938647024835148⟩, true⟩

def words00 : List Nat := [360582078419403613, 360582078263106033, 360582078109762703, 360582077842901814, 360582077575838039, 360582077277306358, 360582077067961384, 360582076985436570, 360582076902790448, 360582076722970885]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 88800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 88800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360610810282065742, 360610862084704462⟩, ⟨(-2559756633019781178), (-2556649544226731588)⟩, true⟩

def words01 : List Nat := [360582076590888163, 360582076585757666, 360582076700240659, 360582076808398248, 360582076811376220, 360582076814481496, 360582076943859364, 360582077142812804, 360582077467929487, 360582077793329374]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 88810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 88800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586448659985028, 360586500474852236⟩, ⟨(-395936053748483867), (-392827878764701327)⟩, true⟩

def words02 : List Nat := [360582078042894026, 360582078198070656, 360582078350128390, 360582078502540826, 360582078533768597, 360582078535050840, 360582078508125983, 360582078403282986, 360582078298201586, 360582078281262558]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 88820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 88800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360559090946939080, 360559142773848373⟩, ⟨2034449484919878052, 2037558729664179598⟩, true⟩

def words03 : List Nat := [360582078436379019, 360582078591737435, 360582078683506502, 360582078684787024, 360582078649916034, 360582078569323510, 360582078488366013, 360582078374742298, 360582078180729248, 360582077923889618]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 88830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 88800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577997000637605, 360578048839639954⟩, ⟨354798494199243188, 357908813348598388⟩, true⟩

def words04 : List Nat := [360582077666765372, 360582077504536448, 360582077511146489, 360582077578473873, 360582077579655050, 360582077539519496, 360582077424899190, 360582077288831598, 360582077152379077, 360582077076143597]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 88840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 88800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk888
