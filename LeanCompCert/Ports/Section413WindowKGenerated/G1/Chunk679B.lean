import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk679A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk679B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk679A

def state06 : KState := ⟨⟨362474527960683224, 362474596345439176⟩, ⟨734305231345337649, 737444036839030875⟩, true⟩

def words05 : List Nat := [371285448342718541, 371285448357523557, 371285448371638462, 371285448373960086, 371285448128571326, 371285447950132040, 371285447805605453, 371285447807942544, 371285447650758275, 371285447493715207]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481794944604889, 362481863350184001⟩, ⟨240448922087954792, 243589142826385580⟩, true⟩

def words06 : List Nat := [371285447392306132, 371285447394864868, 371285447379741047, 371285447401077758, 371285447402876806, 371285447381035124, 371285447137167913, 371285447110883865, 371285447122092379, 371285447124537781]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486843721522830, 362486912148204319⟩, ⟨(-102730463611720122), (-99588808436985368)⟩, true⟩

def words07 : List Nat := [371285447073548459, 371285447015476782, 371285447084322435, 371285447106575340, 371285447194557983, 371285447283448329, 371285447342416704, 371285447344739885, 371285447173160314, 371285447197579336]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488103122915431, 362488171570284279⟩, ⟨(-188335663125555561), (-185192601517432303)⟩, true⟩

def words08 : List Nat := [371285447416022124, 371285447418349608, 371285447413185509, 371285447384050859, 371285447387956289, 371285447390541723, 371285447461865487, 371285447607336239, 371285447746695894, 371285447789173288]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502026102841414, 362502094571246549⟩, ⟨(-1135072954084396174), (-1131928462113998396)⟩, true⟩

def words09 : List Nat := [371285447854112167, 371285447920235086, 371285448201299964, 371285448203622895, 371285448196675539, 371285448155874689, 371285448252371145, 371285448315423077, 371285448561797018, 371285448809241373]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk679B
