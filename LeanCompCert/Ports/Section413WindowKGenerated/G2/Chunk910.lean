import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk910

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581373596384025, 360581428075461435⟩, ⟨48074247661537462, 51421987628770526⟩, true⟩

def state01 : KState := ⟨⟨360585195700151107, 360585250191625312⟩, ⟨(-299793350554769366), (-296444482415561222)⟩, true⟩

def words00 : List Nat := [360581993147104690, 360581993204345203, 360581993289255140, 360581993374408015, 360581993375620352, 360581993358060560, 360581993219706550, 360581993079072673, 360581992938041982, 360581992953682475]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 91000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 91000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589464706127172, 360589519210122832⟩, ⟨(-688371090595445517), (-685021082818855551)⟩, true⟩

def words01 : List Nat := [360581992954855331, 360581992915415550, 360581992875729462, 360581992978617029, 360581993043209721, 360581993108016554, 360581993111292853, 360581993112611206, 360581993158491587, 360581993242677750]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 91010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 91000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580535036085849, 360580589552478234⟩, ⟨124403592151888575, 127754728341441929⟩, true⟩

def words02 : List Nat := [360581993323790975, 360581993325105969, 360581993321404114, 360581993257356630, 360581993193104758, 360581993046580973, 360581993003232822, 360581993031455365, 360581993032629249, 360581992987920852]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 91020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 91000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588824963054929, 360588879491855354⟩, ⟨(-630280323787737969), (-626928058033513783)⟩, true⟩

def words03 : List Nat := [360581992973568053, 360581992971288414, 360581993085411511, 360581993148441473, 360581993149690279, 360581993087168151, 360581993041904095, 360581993121407121, 360581993198116605, 360581993275117473]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 91030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 91000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360578466002257539, 360578520543593652⟩, ⟨312829857828432042, 316183264893669282⟩, true⟩

def words04 : List Nat := [360581993291460117, 360581993313618513, 360581993437362948, 360581993561506116, 360581993637486709, 360581993638801861, 360581993594422938, 360581993456147935, 360581993317639583, 360581993176925818]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 91040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 91000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360562300663716081, 360562355217439403⟩, ⟨1784806282461276030, 1788160817442850088⟩, true⟩

def words05 : List Nat := [360581993196381026, 360581993254236417, 360581993255419395, 360581993237035509, 360581993136635824, 360581993006363630, 360581992875684881, 360581992748744522, 360581992603017185, 360581992388726938]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360562936273640800, 360562990839798035⟩, ⟨1726942617676283578, 1730298284952803988⟩, true⟩

def words06 : List Nat := [360581992174142131, 360581992031451979, 360581991948914563, 360581991864005508, 360581991779001917, 360581991593523628, 360581991287419325, 360581991034706581, 360581990781623150, 360581990491548917]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571974931690202, 360572029510386413⟩, ⟨903717317333548267, 907074126593617061⟩, true⟩

def words07 : List Nat := [360581990284108523, 360581990015569179, 360581989746783767, 360581989563919947, 360581989453837569, 360581989313248170, 360581989172538753, 360581988939174583, 360581988710503488, 360581988602685421]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575293084742660, 360575347675814495⟩, ⟨601468645595060296, 604826582089537914⟩, true⟩

def words08 : List Nat := [360581988505446180, 360581988506761971, 360581988398618787, 360581988217086590, 360581988035320768, 360581987823693268, 360581987707285866, 360581987682200358, 360581987656983856, 360581987554858183]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589944983147780, 360589999586657698⟩, ⟨(-733362064365033841), (-730002994825246093)⟩, true⟩

def words09 : List Nat := [360581987483060479, 360581987321568046, 360581987159692716, 360581987084960607, 360581986941311951, 360581986695259535, 360581986448959949, 360581986323430745, 360581986380081560, 360581986469405141]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk910
