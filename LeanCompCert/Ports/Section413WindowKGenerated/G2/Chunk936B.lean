import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk936A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk936B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk936A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk936B
