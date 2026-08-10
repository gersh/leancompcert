import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk550A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk550B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk550A

def state06 : KState := ⟨⟨362478582898502406, 362478627045083835⟩, ⟨344301586320527120, 345943629155223338⟩, true⟩

def words05 : List Nat := [371284908987326149, 371284909465440888, 371284909941464415, 371284909978517326, 371284909979855581, 371284909977295787, 371284910298482557, 371284910300333959, 371284910187088593, 371284910075035801]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491832309457314, 362491876472636852⟩, ⟨(-385191487089329508), (-383548530278994678)⟩, true⟩

def words06 : List Nat := [371284910177557224, 371284910316386822, 371284910583118543, 371284910850605511, 371284911064180618, 371284911066044771, 371284911184659237, 371284911387214382, 371284911725300164, 371284911853685335]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496415273862143, 362496459453945727⟩, ⟨(-637570008138713531), (-635926120340306891)⟩, true⟩

def words07 : List Nat := [371284911955181825, 371284912057311090, 371284912488018346, 371284912773544103, 371284913155491746, 371284913538151131, 371284913858918997, 371284913860771077, 371284913951962522, 371284914163912135]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475683628634265, 362475727825236806⟩, ⟨504396997648865980, 506041795397935414⟩, true⟩

def words08 : List Nat := [371284914507974520, 371284914509826694, 371284914415025448, 371284914239212084, 371284914062714444, 371284913927615653, 371284913626807951, 371284913603097614, 371284913578738497, 371284913553960675]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489859322161790, 362489903535478069⟩, ⟨(-276555217400052068), (-274909498806518954)⟩, true⟩

def words09 : List Nat := [371284913511501187, 371284913636713655, 371284914015431372, 371284914094889977, 371284914120913299, 371284914147528738, 371284914234572984, 371284914236633547, 371284914250306311, 371284914342926092]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk550B
