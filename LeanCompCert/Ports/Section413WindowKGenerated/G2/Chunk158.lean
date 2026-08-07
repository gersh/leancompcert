import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk158

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360721637973251531, 360721639391465951⟩, ⟨(-2226075485484650069), (-2226060314193018131)⟩, true⟩

def state01 : KState := ⟨⟨360727649730119159, 360727651150224835⟩, ⟨(-2321777175355107062), (-2321761974172350254)⟩, true⟩

def words00 : List Nat := [360580764667962306, 360580766942339211, 360580773216402541, 360580779489731653, 360580783913434621, 360580788458679564, 360580790018299520, 360580791577744036, 360580797135186314, 360580806423504682]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 15800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 15800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360659909338348076, 360659910760326342⟩, ⟨(-1250442874133508469), (-1250427643335550631)⟩, true⟩

def words01 : List Nat := [360580818191858458, 360580829958761756, 360580838541431964, 360580843151384485, 360580846702886109, 360580850253990978, 360580857798367052, 360580864825093684, 360580869821853280, 360580874818013243]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 15810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 15800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360669870379454243, 360669871803308804⟩, ⟨(-1407787893449665783), (-1407772632959346523)⟩, true⟩

def words02 : List Nat := [360580880912814472, 360580889015449073, 360580901107407368, 360580913197875717, 360580921828247042, 360580928403208577, 360580932472234849, 360580936540801338, 360580941125089208, 360580946742797191]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 15820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 15800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360659539497748636, 360659540923498811⟩, ⟨(-1244094754784176602), (-1244079464276887308)⟩, true⟩

def words03 : List Nat := [360580950377176266, 360580954011116399, 360580960114863098, 360580969653983905, 360580978141423681, 360580986627824171, 360580993090067010, 360580995594218420, 360581000553049296, 360581005511323009]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 15830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 15800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360547759555700583, 360547760983327357⟩, ⟨526800508738986834, 526815828980971742⟩, true⟩

def words04 : List Nat := [360581009194224090, 360581009706414544, 360581009706591881, 360581008198747241, 360581006691060009, 360581004137721858, 360581004032217926, 360581002914831881, 360581001797563460, 360580998575061173]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 15840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 15800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360607250721477670, 360607252150983683⟩, ⟨(-416822813446021189), (-416807463408626025)⟩, true⟩

def words05 : List Nat := [360580996478346807, 360580994609921202, 360580993617929824, 360580993618129069, 360580990543432798, 360580983630873535, 360580976719148168, 360580972385889714, 360580971730637239, 360580973387765184]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 15850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 15800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360550009501103287, 360550010932509919⟩, ⟨491172773996912759, 491188154187461021⟩, true⟩

def words06 : List Nat := [360580973387943248, 360580973479025485, 360580976678502208, 360580979877633500, 360580981085657045, 360580981085856549, 360580978346887653, 360580972833822717, 360580967321417337, 360580961666863257]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 15860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 15800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360450177640130597, 360450179073417331⟩, ⟨2076069101232838206, 2076084511269760072⟩, true⟩

def words07 : List Nat := [360580960164533081, 360580960612328584, 360580960612508459, 360580957396006359, 360580950236001806, 360580941784989320, 360580933334977394, 360580928845981877, 360580923106920044, 360580914873875125]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 15870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 15800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360654056104672152, 360654057539845999⟩, ⟨(-1162798773491899405), (-1162783333478111047)⟩, true⟩

def words08 : List Nat := [360580906641822169, 360580902369646706, 360580900114903226, 360580897720825851, 360580895327034189, 360580889495602180, 360580883287465104, 360580881036023413, 360580880489070872, 360580885094217775]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 15880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 15800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360533537619174188, 360533539056249800⟩, ⟨753017981126059958, 753033451368438600⟩, true⟩

def words09 : List Nat := [360580887693864417, 360580890293205912, 360580894660368548, 360580901031579021, 360580903938925227, 360580906845936675, 360580906846117742, 360580906703718323, 360580902629288786, 360580899650675488]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 15890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 15800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 15800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk158
