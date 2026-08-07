import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk724

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586067773717053, 360586101648032479⟩, ⟨(-271289483731383553), (-269632953812024389)⟩, true⟩

def state01 : KState := ⟨⟨360598630667891452, 360598664551928258⟩, ⟨(-1180917308956255117), (-1179260075160953741)⟩, true⟩

def words00 : List Nat := [360582377535945212, 360582377727250270, 360582377983916228, 360582378240771136, 360582378336247368, 360582378337275813, 360582378441060992, 360582378561031443, 360582378677703914, 360582378903681984]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575608001021452, 360575641894842555⟩, ⟨486255716659728107, 487913658983618773⟩, true⟩

def words01 : List Nat := [360582379034591764, 360582379165610312, 360582379251595666, 360582379443422496, 360582379503294844, 360582379563319093, 360582379564235454, 360582379509635045, 360582379264508034, 360582379172652327]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578226314415848, 360578260217934964⟩, ⟨296680561910967700, 298339206614138312⟩, true⟩

def words02 : List Nat := [360582379177739046, 360582379284720663, 360582379285650004, 360582379272442135, 360582379259061112, 360582379232481968, 360582379276934132, 360582379321582568, 360582379322514954, 360582379218440475]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598740557098610, 360598774470323704⟩, ⟨(-1189280424884889408), (-1187621077128699218)⟩, true⟩

def words03 : List Nat := [360582379295810163, 360582379430356426, 360582379719693264, 360582379818977828, 360582379819932959, 360582379731851743, 360582379643555504, 360582379693828904, 360582379920982792, 360582380148363369]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589152298268093, 360589186221318595⟩, ⟨(-494783985215531025), (-493123925662229109)⟩, true⟩

def words04 : List Nat := [360582380279249511, 360582380308825110, 360582380309671475, 360582380297627228, 360582380285310813, 360582380224868216, 360582380210361756, 360582380060665414, 360582379910780292, 360582379911872732]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk724
