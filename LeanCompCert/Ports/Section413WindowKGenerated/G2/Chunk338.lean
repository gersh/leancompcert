import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk338

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360661346390137026, 360661353330714852⟩, ⟨(-2705156355552820740), (-2704997743153598734)⟩, true⟩

def state01 : KState := ⟨⟨360601113916237795, 360601120861124572⟩, ⟨(-669389762869213786), (-669231004806659524)⟩, true⟩

def words00 : List Nat := [360581327997479569, 360581328943665982, 360581329427575833, 360581329911585636, 360581330173308220, 360581330173760350, 360581329563714374, 360581328412246702, 360581327260760662, 360581327568858545]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578151186631617, 360578158135774394⟩, ⟨107287379047316008, 107446281026449176⟩, true⟩

def words01 : List Nat := [360581329028494473, 360581330488130661, 360581331295905866, 360581332366327450, 360581333214746539, 360581334063235064, 360581334886534919, 360581335233013828, 360581335233416672, 360581335139944307]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360668994194652629, 360669001148063984⟩, ⟨(-2965575828212441109), (-2965416781849013583)⟩, true⟩

def words02 : List Nat := [360581335471918514, 360581336336232980, 360581337827406709, 360581339318586602, 360581339900055183, 360581340233490682, 360581341439692625, 360581342645955631, 360581344724838234, 360581347316316504]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360641040794746849, 360641047752475612⟩, ⟨(-2019773642976520172), (-2019614450533869070)⟩, true⟩

def words03 : List Nat := [360581349231299594, 360581351146207891, 360581353455587065, 360581356206275807, 360581358546326460, 360581360886315588, 360581362786793373, 360581364709814317, 360581366473866013, 360581368237965584]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588994241246657, 360589001203232134⟩, ⟨(-258283417057205406), (-258124080545309664)⟩, true⟩

def words04 : List Nat := [360581370542941251, 360581371978033173, 360581372874392499, 360581373770748038, 360581374060877593, 360581374791804778, 360581375232124995, 360581375672502438, 360581375676011427, 360581375901747827]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360632948930551252, 360632955896818375⟩, ⟨(-1746366687358412370), (-1746207205892961874)⟩, true⟩

def words05 : List Nat := [360581376999176664, 360581378096684386, 360581379790830839, 360581380615720540, 360581380616138176, 360581380595916210, 360581381426404683, 360581382984612545, 360581384508107210, 360581386031607869]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360625304650423481, 360625311621000310⟩, ⟨(-1487699116633443802), (-1487539489219695224)⟩, true⟩

def words06 : List Nat := [360581387116171540, 360581387331785020, 360581388418472760, 360581389505230158, 360581390107034356, 360581391093441464, 360581391530429145, 360581391967436663, 360581392533114204, 360581393830287911]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360580066950608868, 360580073925458876⟩, ⟨44845032568254098, 45004804735829692⟩, true⟩

def words07 : List Nat := [360581395998041404, 360581398165754037, 360581399667143957, 360581400299914090, 360581400678438501, 360581401057064465, 360581401814048520, 360581402322837094, 360581402323241270, 360581402284512472]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596181747775313, 360596188726894840⟩, ⟨(-501197928834113700), (-501038011993299712)⟩, true⟩

def words08 : List Nat := [360581402487121568, 360581403168993334, 360581404369694978, 360581405570412374, 360581406017161960, 360581406017615164, 360581405596400385, 360581404935449272, 360581404482932353, 360581404919630573]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360614826710235258, 360614833693672366⟩, ⟨(-1133220622290541617), (-1133060559105805161)⟩, true⟩

def words09 : List Nat := [360581404920038968, 360581404616002859, 360581404877157576, 360581406127340476, 360581407156073119, 360581408184819973, 360581408775679746, 360581409091499014, 360581410077842212, 360581411064277782]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk338
