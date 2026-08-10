import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk213A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk213B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk213A

def state06 : KState := ⟨⟨360509511295688117, 360509513959373302⟩, ⟨1515227613644349436, 1515266112685215440⟩, true⟩

def words05 : List Nat := [360580465502828016, 360580463415398285, 360580461328110884, 360580461320652572, 360580461323456494, 360580461326305570, 360580461326557397, 360580459675804695, 360580456705100660, 360580453384124483]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360517897076979683, 360517899743255892⟩, ⟨1336113469603190028, 1336152024001685632⟩, true⟩

def words06 : List Nat := [360580450063368700, 360580447973597927, 360580445596012120, 360580442126778489, 360580438657820052, 360580434644499891, 360580431740968904, 360580429818542308, 360580427896266247, 360580424405118395]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360530581631190259, 360530584300070021⟩, ⟨1064451002282587104, 1064489612331761702⟩, true⟩

def words07 : List Nat := [360580421479667328, 360580417761068294, 360580414042737280, 360580409659514146, 360580403098236630, 360580394729578739, 360580386361651274, 360580380171578324, 360580375665720321, 360580373337129505]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360518793768682402, 360518796440186067⟩, ⟨1316097267744380149, 1316135933905296573⟩, true⟩

def words08 : List Nat := [360580371008716956, 360580367590224488, 360580361994505701, 360580358575416105, 360580355156573782, 360580349891499661, 360580344561468402, 360580338142811018, 360580331724701302, 360580326871878695]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360490054217042593, 360490056891146122⟩, ⟨1931189734017768917, 1931228455803025943⟩, true⟩

def words09 : List Nat := [360580323995638314, 360580323293832137, 360580322592058997, 360580320785350365, 360580318117384700, 360580314003989846, 360580309890899130, 360580307951495406, 360580305428446392, 360580301211510750]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk213B
