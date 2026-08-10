import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk656A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk656B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk656A

def state06 : KState := ⟨⟨362505663050459930, 362505726713068982⟩, ⟨(-1330823444917279749), (-1328000159928502755)⟩, true⟩

def words05 : List Nat := [371285499482113206, 371285499762463749, 371285500130395187, 371285500261415970, 371285500353784561, 371285500446852534, 371285500770789686, 371285500994937784, 371285501304503060, 371285501615066690]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483502662071863, 362483566344865834⟩, ⟨124280961987168934, 127105572415885118⟩, true⟩

def words06 : List Nat := [371285501918284228, 371285501920521213, 371285502060740273, 371285502209636044, 371285502379293352, 371285502381530436, 371285502242352212, 371285502050817407, 371285501861901139, 371285501864470157]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477708153036107, 362477771855976853⟩, ⟨504890417210546412, 507716350782909322⟩, true⟩

def words07 : List Nat := [371285501954341832, 371285502074608695, 371285502193558892, 371285502195835462, 371285502121986457, 371285502084171837, 371285502236389244, 371285502238626966, 371285502122633050, 371285502007480856]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473519063177973, 362473582786181972⟩, ⟨780066439267278556, 782893690693165534⟩, true⟩

def words08 : List Nat := [371285501891343483, 371285501800869297, 371285501609023114, 371285501586772147, 371285501563847321, 371285501494264412, 371285501115206790, 371285500968971207, 371285500821510919, 371285500790302739]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475769173136730, 362475832916506885⟩, ⟨632260123102470656, 635088712484143292⟩, true⟩

def words09 : List Nat := [371285500610568081, 371285500428426547, 371285500270368028, 371285500272834296, 371285500183615625, 371285500106100640, 371285500027801311, 371285499932869606, 371285499555726583, 371285499411369658]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk656B
