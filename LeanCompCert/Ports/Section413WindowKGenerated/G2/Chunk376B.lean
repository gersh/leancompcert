import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk376A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk376B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk376A

def state06 : KState := ⟨⟨360611722028197718, 360611730721501148⟩, ⟨(-1136946477505640622), (-1136725174780386260)⟩, true⟩

def words05 : List Nat := [360581536802161488, 360581539129197174, 360581540766770318, 360581541930287947, 360581542677236488, 360581543424283681, 360581544875909730, 360581546032264937, 360581546834222558, 360581547636219813]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360649028239057997, 360649036937150554⟩, ⟨(-2542059309533428144), (-2541837826425702210)⟩, true⟩

def words06 : List Nat := [360581548646928578, 360581550010929497, 360581552079231734, 360581554147524752, 360581555633418233, 360581556728814757, 360581557801657743, 360581558874585617, 360581560487821489, 360581562279551189]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360628466230672195, 360628474933603692⟩, ⟨(-1767341718231614719), (-1767120052818174503)⟩, true⟩

def words07 : List Nat := [360581563632066831, 360581564984567152, 360581566841090408, 360581569297900335, 360581571257645378, 360581573217365895, 360581574758115442, 360581575597365375, 360581576842450909, 360581578087638400]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600189386084825, 360600198093805541⟩, ⟨(-701810431235962443), (-701588585340546831)⟩, true⟩

def words08 : List Nat := [360581579304115481, 360581580035795000, 360581580342267089, 360581580648774062, 360581580775002221, 360581581446973662, 360581582254700319, 360581583062488171, 360581583378890154, 360581583873292938]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360646013825314421, 360646022537832246⟩, ⟨(-2429161456507029653), (-2428939429785238409)⟩, true⟩

def words09 : List Nat := [360581585070973847, 360581586268745662, 360581588169681502, 360581589615311819, 360581590385233651, 360581591155147772, 360581591719872906, 360581592726292189, 360581594435716829, 360581596145169313]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk376B
