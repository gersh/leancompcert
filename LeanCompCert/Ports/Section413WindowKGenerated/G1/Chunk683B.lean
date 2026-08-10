import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk683A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk683B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk683A

def state06 : KState := ⟨⟨362498371458001503, 362498440681933944⟩, ⟨(-890715977286251943), (-887519973277261571)⟩, true⟩

def words05 : List Nat := [371285457360074199, 371285457331196066, 371285457429347222, 371285457431710414, 371285457431911568, 371285457397634257, 371285457462001448, 371285457464575637, 371285457648666850, 371285457841231245]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486634639332303, 362486703884366209⟩, ⟨(-88319935540394977), (-85122488927740429)⟩, true⟩

def words06 : List Nat := [371285458033172751, 371285458090017814, 371285458339900725, 371285458590990311, 371285458854065226, 371285458856401794, 371285458834561189, 371285458812577693, 371285458854802708, 371285458875679372]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483201361678473, 362483270627736807⟩, ⟨146504366404177900, 149703250562564536⟩, true⟩

def words07 : List Nat := [371285459109094099, 371285459343431591, 371285459567084635, 371285459572060958, 371285459635532213, 371285459700245368, 371285459950195716, 371285459952532914, 371285459941293523, 371285459911892446]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486691601393377, 362486760888390555⟩, ⟨(-92180025090932289), (-88979709026570939)⟩, true⟩

def words08 : List Nat := [371285459951121051, 371285459953722857, 371285460020126521, 371285460099938147, 371285460127733376, 371285460130072660, 371285459917328618, 371285459815956155, 371285459822775671, 371285459844261554]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489594837977920, 362489664146313023⟩, ⟨(-290758862605138891), (-287557087136987723)⟩, true⟩

def words09 : List Nat := [371285459846031847, 371285459832902571, 371285459944454588, 371285459965778537, 371285460051235980, 371285460137565212, 371285460178959737, 371285460181313565, 371285460092366220, 371285460156793324]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk683B
