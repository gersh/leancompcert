import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk393A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk393B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk393A

def state06 : KState := ⟨⟨360617907365338163, 360617916895456701⟩, ⟨(-1400998656989294482), (-1400745122886936206)⟩, true⟩

def words05 : List Nat := [360582323709099108, 360582324346135922, 360582324906132489, 360582325970173932, 360582326652408196, 360582327334693482, 360582327693084444, 360582327953569239, 360582328858190585, 360582329762942616]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360603325703400370, 360603335238542207⟩, ⟨(-827140976358347457), (-826887244513861123)⟩, true⟩

def words06 : List Nat := [360582330649369336, 360582330894089220, 360582330894563756, 360582330816412456, 360582330738175814, 360582330577055321, 360582331301896523, 360582332026813432, 360582332259973723, 360582332793988758]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360640438107987214, 360640447648156751⟩, ⟨(-2288433887931973936), (-2288179958122538156)⟩, true⟩

def words07 : List Nat := [360582333971725773, 360582335149560528, 360582336971015361, 360582338150996423, 360582338720853058, 360582339290709544, 360582340005415664, 360582341043190689, 360582342519157621, 360582343995173777]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360637574382517514, 360637583927766024⟩, ⟨(-2175633307025421554), (-2175379177181339138)⟩, true⟩

def words08 : List Nat := [360582345148447359, 360582346586324641, 360582348667503884, 360582350748738898, 360582352666467354, 360582354175449173, 360582355295055347, 360582356414662178, 360582357240758475, 360582358643381740]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580262454525959, 360580272004790501⟩, ⟨82225160741528626, 82479488192482598⟩, true⟩

def words09 : List Nat := [360582360142564541, 360582361641770430, 360582362810827924, 360582363339077873, 360582363704189030, 360582364069433021, 360582365077519884, 360582365444920660, 360582365445396229, 360582365392815691]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk393B
