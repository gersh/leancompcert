import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk772A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk772B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk772A

def state06 : KState := ⟨⟨362475137271223410, 362475226539214642⟩, ⟨765959262904747662, 770616627931371172⟩, true⟩

def words05 : List Nat := [371285200766962929, 371285200913306293, 371285201025476133, 371285201028146674, 371285200977052362, 371285200978541081, 371285201095509698, 371285201098174383, 371285200993952373, 371285200867818466]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 77250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 77200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362498073707243885, 362498162999067415⟩, ⟨(-1006191467242774525), (-1001532260810030961)⟩, true⟩

def words06 : List Nat := [371285200778802948, 371285200781739859, 371285200878641603, 371285201012815582, 371285201094164053, 371285201096875540, 371285201146065844, 371285201256594196, 371285201533116830, 371285201703616211]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 77260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 77200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491195605337342, 362491284921520446⟩, ⟨(-474690030473968911), (-470028941663055695)⟩, true⟩

def words07 : List Nat := [371285201864027792, 371285202025372434, 371285202229827009, 371285202358566820, 371285202494821232, 371285202632054152, 371285202768506412, 371285202771171780, 371285202763073385, 371285202845180039]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 77270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 77200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482440109849350, 362482529449743425⟩, ⟨202017093805729497, 206680015125348993⟩, true⟩

def words08 : List Nat := [371285203079913698, 371285203144081435, 371285203210415621, 371285203277604074, 371285203342114181, 371285203349553095, 371285203409849181, 371285203471220500, 371285203531795137, 371285203534555501]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 77280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 77200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502708681257630, 362502798045229181⟩, ⟨(-1364614783448658592), (-1359950001057379396)⟩, true⟩

def words09 : List Nat := [371285203634424331, 371285203770277064, 371285204034753850, 371285204160986641, 371285204259684647, 371285204359245407, 371285204544671639, 371285204669233709, 371285204898645517, 371285205129211829]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 77290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 77200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 77200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk772B
