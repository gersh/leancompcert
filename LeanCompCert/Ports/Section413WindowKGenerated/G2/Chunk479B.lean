import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk479A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk479B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk479A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk479B
