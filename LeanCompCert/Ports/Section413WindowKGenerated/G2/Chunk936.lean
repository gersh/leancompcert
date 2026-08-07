import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk936

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589233422019073, 360589291185619382⟩, ⟨(-679624261942151255), (-675973339067355883)⟩, true⟩

def state01 : KState := ⟨⟨360605743175582244, 360605800951935083⟩, ⟨(-2225057534208495826), (-2221405417632595414)⟩, true⟩

def words00 : List Nat := [360582069517742799, 360582069671450088, 360582069754154086, 360582069837027432, 360582069871505932, 360582069963297320, 360582070168780136, 360582070374518398, 360582070521958508, 360582070776874112]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602294152137748, 360602351941295389⟩, ⟨(-1902260036457877045), (-1898606721161424359)⟩, true⟩

def words01 : List Nat := [360582071000743697, 360582071224988426, 360582071434127407, 360582071529699260, 360582071530949164, 360582071528419047, 360582071616200228, 360582071795647089, 360582072013367398, 360582072231388836]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595439009089843, 360595496811141446⟩, ⟨(-1260567368010704237), (-1256912845517712711)⟩, true⟩

def words02 : List Nat := [360582072363738804, 360582072382425435, 360582072494699450, 360582072607369873, 360582072638923044, 360582072642776416, 360582072643995272, 360582072577253763, 360582072556198655, 360582072701118936]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360572949660185245, 360573007475025518⟩, ⟨845275875461730222, 848931595420021510⟩, true⟩

def words03 : List Nat := [360582072938510502, 360582073176192853, 360582073332855060, 360582073375880851, 360582073377015265, 360582073373939024, 360582073479877071, 360582073481232539, 360582073478122741, 360582073382708347]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593472756948491, 360593530584570220⟩, ⟨(-1076626039971381962), (-1072969123092782010)⟩, true⟩

def words04 : List Nat := [360582073286989317, 360582073274810023, 360582073314655537, 360582073354753266, 360582073356015058, 360582073298286983, 360582073252974623, 360582073264337601, 360582073358145539, 360582073481890134]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360579901269961525, 360579959110519175⟩, ⟨194392356800022117, 198050485188627297⟩, true⟩

def words05 : List Nat := [360582073529451775, 360582073577163122, 360582073578281093, 360582073669246305, 360582073733598317, 360582073798172213, 360582073805334113, 360582073806689884, 360582073700017263, 360582073679013609]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360573017968702793, 360573075822021603⟩, ⟨839079326394867750, 842738650057671650⟩, true⟩

def words06 : List Nat := [360582073728142582, 360582073729498402, 360582073687609298, 360582073587860861, 360582073487906573, 360582073289451981, 360582073161133231, 360582073030405673, 360582072899532894, 360582072711634688]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360600954914554645, 360601012780670844⟩, ⟨(-1777926273934158704), (-1774265751475636892)⟩, true⟩

def words07 : List Nat := [360582072616683317, 360582072599185081, 360582072658009977, 360582072738924130, 360582072740176154, 360582072723924062, 360582072783211663, 360582072933044069, 360582073136317745, 360582073339893359]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587795293545607, 360587853172604847⟩, ⟨(-545136916587677582), (-541475181563480028)⟩, true⟩

def words08 : List Nat := [360582073454630547, 360582073501301081, 360582073661588752, 360582073822272267, 360582073928766071, 360582073947688052, 360582073948907756, 360582073862200663, 360582073775213708, 360582073800183126]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360568989306849383, 360569047198670811⟩, ⟨1216901499962960682, 1220564430742219886⟩, true⟩

def words09 : List Nat := [360582073896856165, 360582073993782259, 360582074033380670, 360582074034737207, 360582073992355821, 360582073871870130, 360582073750988720, 360582073703304075, 360582073637576318, 360582073499959416]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk936
