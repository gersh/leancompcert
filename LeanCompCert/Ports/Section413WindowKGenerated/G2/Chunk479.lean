import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk479

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580551783222943, 360580566126582363⟩, ⟨96963730387384936, 97427993799599610⟩, true⟩

def state01 : KState := ⟨⟨360564840288021895, 360564854637665000⟩, ⟨849462635053311149, 849927199485396367⟩, true⟩

def words00 : List Nat := [360582600072061678, 360582599692368261, 360582599052836218, 360582598848095410, 360582598643195149, 360582598059015444, 360582597338677276, 360582596397687177, 360582595456598845, 360582594716969642]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 47900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 47900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360552937729922357, 360552952085770546⟩, ⟨1419800326184095344, 1420265187932711326⟩, true⟩

def words01 : List Nat := [360582594411389376, 360582594476204390, 360582594476791617, 360582594324618107, 360582593737295710, 360582592800086197, 360582591862710995, 360582591359815824, 360582590958769401, 360582590340944434]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 47910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 47900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360564702956996454, 360564717319073758⟩, ⟨856091292695361549, 856556452973829887⟩, true⟩

def words02 : List Nat := [360582589722995977, 360582589539461155, 360582589773809815, 360582590008273565, 360582590008888406, 360582589861340989, 360582589459695562, 360582589125642309, 360582588791419273, 360582588307034823]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 47920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 47900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360581292893864545, 360581307262222490⟩, ⟨60805287194385085, 61270748534742389⟩, true⟩

def words03 : List Nat := [360582587934776782, 360582587284801303, 360582586634725754, 360582586423730359, 360582586424282301, 360582586320897081, 360582586217434446, 360582585819687632, 360582585359645938, 360582585333739694]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 47930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 47900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583629929989454, 360583644304565231⟩, ⟨(-51340306873715607), (-50874547419454967)⟩, true⟩

def words04 : List Nat := [360582585619755090, 360582585620414694, 360582585498627327, 360582585043291618, 360582584587864441, 360582583923985662, 360582583568104206, 360582583607445851, 360582583608037376, 360582583335087651]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 47940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 47900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360591302415594412, 360591316796397352⟩, ⟨(-419250362128561057), (-418784304051591283)⟩, true⟩

def words05 : List Nat := [360582583791470444, 360582584248035367, 360582585021452351, 360582585360599086, 360582585361208224, 360582585295779471, 360582585230239437, 360582584837877038, 360582584846083929, 360582585028835133]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 47950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 47900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587755538999870, 360587769926087918⟩, ⟨(-249331742417478705), (-248865382876545871)⟩, true⟩

def words06 : List Nat := [360582585029428552, 360582584979518346, 360582584495255432, 360582584444683377, 360582584393926448, 360582584167205661, 360582583715886072, 360582582995484230, 360582582274986090, 360582582096297492]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 47960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 47900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567555251179264, 360567569644489549⟩, ⟨719678449200609398, 720145107253111548⟩, true⟩

def words07 : List Nat := [360582582096844321, 360582581950411097, 360582581803911781, 360582581441055055, 360582580985518070, 360582580289150461, 360582579592618522, 360582579329516897, 360582579233569568, 360582578921422711]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 47970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 47900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601480736808358, 360601495136347471⟩, ⟨(-908175279109007786), (-907708322166369456)⟩, true⟩

def words08 : List Nat := [360582578729543757, 360582579181319028, 360582579761279146, 360582580341339002, 360582580515262932, 360582580515923263, 360582580288652554, 360582580322134336, 360582580605091655, 360582580999901755]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 47980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 47900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360566891346476073, 360566905752312161⟩, ⟨751969820124575336, 752437079290470682⟩, true⟩

def words09 : List Nat := [360582581087245347, 360582581174667337, 360582581329147071, 360582581751982014, 360582581963267167, 360582582174653996, 360582582175247813, 360582582166556785, 360582581850628867, 360582581524797380]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 47990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 47900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 47900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk479
