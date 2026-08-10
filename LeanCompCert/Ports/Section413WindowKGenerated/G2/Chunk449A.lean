import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk449A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590552569730641, 360590565105649037⟩, ⟨(-331215639440317481), (-330835272879542097)⟩, true⟩

def state01 : KState := ⟨⟨360596968412088918, 360596980953858874⟩, ⟨(-619444708363246371), (-619064079038010043)⟩, true⟩

def words00 : List Nat := [360583197001418533, 360583197023576310, 360583197498269590, 360583197973121629, 360583198105344662, 360583198105959143, 360583197743319304, 360583197132209654, 360583196521009597, 360583196712157777]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 44900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 44900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568711566706413, 360568724114272732⟩, ⟨649797531203338028, 650178420872078792⟩, true⟩

def words01 : List Nat := [360583197376481257, 360583198040903322, 360583198325798159, 360583198447127384, 360583198447644262, 360583198300142564, 360583198499335868, 360583198576460010, 360583198577023392, 360583198255431951]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 44910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 44900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360635663929580428, 360635676482947739⟩, ⟨(-2358065347670073063), (-2357684197391394817)⟩, true⟩

def words02 : List Nat := [360583197933716205, 360583198069757821, 360583198644091056, 360583199218520453, 360583199361598251, 360583199521676373, 360583200176414492, 360583200831313608, 360583201872977154, 360583203041506610]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 44920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 44900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598783692747650, 360598796251975067⟩, ⟨(-700907881670907875), (-700526468068896101)⟩, true⟩

def words03 : List Nat := [360583203864058488, 360583204686639639, 360583205454633811, 360583206472746498, 360583207068914223, 360583207665151212, 360583208012047656, 360583208012662576, 360583208212364165, 360583208559932859]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 44930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 44900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590226396504998, 360590238961523361⟩, ⟨(-316365226299723523), (-315983552424066773)⟩, true⟩

def words04 : List Nat := [360583209049664977, 360583209317668796, 360583209318216745, 360583209290945241, 360583209263574701, 360583209151056748, 360583209281229053, 360583209411506303, 360583209412054286, 360583209450446321]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 44940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 44900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk449A
