import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk724A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk724A
