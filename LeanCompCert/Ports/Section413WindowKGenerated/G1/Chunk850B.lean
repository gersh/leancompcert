import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk850A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk850B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk850A

def state06 : KState := ⟨⟨362463836937208776, 362463945943298081⟩, ⟨1810222039249132408, 1816482678441617846⟩, true⟩

def words05 : List Nat := [371285302255131364, 371285302237011124, 371285302217898252, 371285302199451240, 371285302046967169, 371285301938311364, 371285301828118274, 371285301748130704, 371285301501186319, 371285301253413784]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469199216503545, 362469308249027825⟩, ⟨1354097479498980994, 1360360367382111648⟩, true⟩

def words06 : List Nat := [371285301004358773, 371285300894671850, 371285300714790603, 371285300566467242, 371285300417141376, 371285300247255169, 371285299892244273, 371285299663577224, 371285299433372410, 371285299319527204]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475847726188771, 362475956785701899⟩, ⟨788468827271905642, 794734011231886308⟩, true⟩

def words07 : List Nat := [371285299133801462, 371285298922607283, 371285298710160442, 371285298624465567, 371285298489396952, 371285298377179435, 371285298264019112, 371285298139522346, 371285297912153298, 371285297806050182]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473821355746960, 362473930441576249⟩, ⟨960902612673320655, 967170035748223845⟩, true⟩

def words08 : List Nat := [371285297726507067, 371285297729469261, 371285297616928179, 371285297503307318, 371285297388649797, 371285297246579027, 371285297050033984, 371285296992758553, 371285296934444181, 371285296877535213]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491298240048948, 362491407352603699⟩, ⟨(-526264621113603382), (-519994923834885262)⟩, true⟩

def words09 : List Nat := [371285296750394075, 371285296758394832, 371285296902840482, 371285296905797027, 371285296880485310, 371285296836915907, 371285296858840306, 371285296876820844, 371285296950664319, 371285297025770467]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk850B
