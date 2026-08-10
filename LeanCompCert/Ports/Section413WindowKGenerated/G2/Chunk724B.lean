import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk724A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk724B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk724A

def state06 : KState := ⟨⟨360551401135693221, 360551435068420838⟩, ⟨2240585386608358386, 2242246147318456586⟩, true⟩

def words05 : List Nat := [360582380137555793, 360582380363429554, 360582380494414503, 360582380562287046, 360582380563148610, 360582380545380088, 360582380527330496, 360582380408954656, 360582380100371924, 360582379674373343]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598503302250651, 360598537244692234⟩, ⟨(-1172663960141275088), (-1171002495509063824)⟩, true⟩

def words06 : List Nat := [360582379248153514, 360582379012345568, 360582378937301971, 360582378977852262, 360582378978801512, 360582378857020107, 360582378652528604, 360582378638428937, 360582378798815252, 360582379022844750]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588075509509176, 360588109461765269⟩, ⟨(-416949629586761637), (-415287453648857351)⟩, true⟩

def words07 : List Nat := [360582379062128890, 360582379101504384, 360582379208279323, 360582379427264366, 360582379529582502, 360582379632060434, 360582379638284049, 360582379697289279, 360582379777180110, 360582379857404832]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587769599460187, 360587803561407635⟩, ⟨(-394822579097792192), (-393159700681473082)⟩, true⟩

def words08 : List Nat := [360582380127287413, 360582380207362876, 360582380208280493, 360582380166634216, 360582380124838368, 360582379938014549, 360582379905702509, 360582379966742244, 360582379967659672, 360582379995714219]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360611948318133535, 360611982289801929⟩, ⟨(-2147652310358417335), (-2145988727223051083)⟩, true⟩

def words09 : List Nat := [360582380208354393, 360582380421310346, 360582380823876586, 360582381097282324, 360582381208853964, 360582381320494015, 360582381621854630, 360582382035094397, 360582382444220679, 360582382853556594]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk724B
