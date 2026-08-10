import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk781A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360554312379542485, 360554352034371856⟩, ⟨2175520468211328010, 2177612204970007910⟩, true⟩

def state01 : KState := ⟨⟨360590431696422643, 360590471361773369⟩, ⟨(-645553465264787381), (-643460906736509793)⟩, true⟩

def words00 : List Nat := [360582234036848153, 360582233844806359, 360582233750139796, 360582233766662315, 360582233767691672, 360582233632300904, 360582233504660780, 360582233472531156, 360582233479339059, 360582233585957716]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 78100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 78100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360572123213868298, 360572162889869227⟩, ⟨784584616312318721, 786678006777977115⟩, true⟩

def words01 : List Nat := [360582233586968763, 360582233565771182, 360582233544376434, 360582233588283951, 360582233589220255, 360582233561613631, 360582233533890818, 360582233401807559, 360582233140443616, 360582233012843856]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 78110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 78100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586156514165878, 360586196200667913⟩, ⟨(-311739983271812992), (-309645772406218004)⟩, true⟩

def words02 : List Nat := [360582232919557385, 360582232986185557, 360582232987179742, 360582232971938361, 360582232956516745, 360582232944942856, 360582232986553021, 360582233028362375, 360582233029365918, 360582233039151918]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 78120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 78100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360610256502985463, 360610296200014972⟩, ⟨(-2194883357779868246), (-2192788324349341976)⟩, true⟩

def words03 : List Nat := [360582233097774690, 360582233156724930, 360582233241059741, 360582233329816676, 360582233330845972, 360582233279622561, 360582233339399805, 360582233536234868, 360582233896270269, 360582234256549323]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 78130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 78100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591147459699228, 360591187167372801⟩, ⟨(-701719508185300656), (-699623642974978038)⟩, true⟩

def words04 : List Nat := [360582234483586720, 360582234589818611, 360582234744518512, 360582234899546489, 360582235013308170, 360582235032581601, 360582235033587498, 360582234953735350, 360582234873654685, 360582234964035992]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 78140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 78100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk781A
