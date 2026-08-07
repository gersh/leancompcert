import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk393

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360591111140741248, 360591120640643767⟩, ⟨(-347133981312706075), (-346881635606540629)⟩, true⟩

def state01 : KState := ⟨⟨360582430162618542, 360582439667524330⟩, ⟨(-5929978829711750), (-5677436469168638)⟩, true⟩

def words00 : List Nat := [360582295231558425, 360582295708816952, 360582295709298290, 360582295688473106, 360582295667568556, 360582295206031845, 360582295233076045, 360582295398261375, 360582295398735234, 360582295243915947]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360622308533211191, 360622318043146409⟩, ⟨(-1573710448552178626), (-1573457708459785334)⟩, true⟩

def words01 : List Nat := [360582295526876156, 360582295809995695, 360582296738545579, 360582297569679515, 360582297847941840, 360582298126231645, 360582299049946940, 360582300297340704, 360582301315523943, 360582302333768220]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360615314725662997, 360615324240670662⟩, ⟨(-1298939614835729715), (-1298686675270910261)⟩, true⟩

def words02 : List Nat := [360582302889546136, 360582302890078304, 360582303360381953, 360582303918581754, 360582303945155508, 360582304087548290, 360582304088022344, 360582303907021049, 360582303983883666, 360582304824045840]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598399227040057, 360598408747067886⟩, ⟨(-633566460578613202), (-633313323546027970)⟩, true⟩

def words03 : List Nat := [360582306034343031, 360582307244680318, 360582307956457116, 360582308231942803, 360582308343501280, 360582308455198773, 360582309079992132, 360582309879164342, 360582310288867751, 360582310698631242]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360623626115361678, 360623635640409595⟩, ⟨(-1625944210652501629), (-1625690876104871799)⟩, true⟩

def words04 : List Nat := [360582311752964425, 360582313177366308, 360582315246227550, 360582317315085532, 360582318799954044, 360582319836613873, 360582320491872671, 360582321147248936, 360582322021659498, 360582323072085922]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk393
