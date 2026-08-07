import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk213

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584103667229535, 360584106315309487⟩, ⟨(-74740352587977359), (-74702186407148533)⟩, true⟩

def state01 : KState := ⟨⟨360479739429141278, 360479742079808676⟩, ⟨2148502574579468487, 2148540795886066099⟩, true⟩

def words00 : List Nat := [360580599335281203, 360580598479136392, 360580595428310719, 360580591221438887, 360580587014917315, 360580582261731142, 360580578926533366, 360580574717894992, 360580570509617035, 360580565204908914]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360603806956260645, 360603809609520879⟩, ⟨(-496232061884262082), (-496193785311878796)⟩, true⟩

def words01 : List Nat := [360580560474094398, 360580557260444296, 360580554047012855, 360580553023389160, 360580549807212511, 360580544469593628, 360580539132423122, 360580535984675492, 360580535979530192, 360580537071398283]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360552973095383240, 360552975751263488⟩, ⟨587765284046004911, 587803616489927317⟩, true⟩

def words02 : List Nat := [360580537071645578, 360580536692396879, 360580538286381903, 360580540177412135, 360580541455937613, 360580541456212384, 360580540544669801, 360580538538821792, 360580536533114397, 360580533351661516]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360448756875865326, 360448759534333849⟩, ⟨2811380994130947919, 2811419381795895705⟩, true⟩

def words03 : List Nat := [360580532341516863, 360580532623302083, 360580532623548064, 360580531459210700, 360580528106205732, 360580523380464834, 360580518655082109, 360580514881953313, 360580509821399127, 360580503647820068]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360571384788178334, 360571387449244580⟩, ⟨193787073679362039, 193825516792806777⟩, true⟩

def words04 : List Nat := [360580497474755793, 360580493486803125, 360580490607753858, 360580487669254429, 360580484731008175, 360580479884272108, 360580474457513304, 360580471214725212, 360580467972158105, 360580465927782885]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk213
