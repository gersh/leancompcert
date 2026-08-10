import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk825A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk825B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk825A

def state06 : KState := ⟨⟨362486469600856143, 362486572057896727⟩, ⟨(-113250894200570019), (-107539175473779605)⟩, true⟩

def words05 : List Nat := [371285269688446405, 371285269631912601, 371285269636051721, 371285269639204659, 371285269629918082, 371285269623606689, 371285269616375592, 371285269609770430, 371285269496463876, 371285269515831179]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482791371788546, 362482893854297309⟩, ⟨190455612984381742, 196169434496711928⟩, true⟩

def words06 : List Nat := [371285269680343317, 371285269683204482, 371285269652339370, 371285269619070932, 371285269584769088, 371285269554076143, 371285269533452324, 371285269598686556, 371285269646831478, 371285269649798057]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497373879108704, 362497476387490957⟩, ⟨(-1013646785474171563), (-1007930827455673305)⟩, true⟩

def words07 : List Nat := [371285269740956576, 371285269862396803, 371285270110510718, 371285270239478042, 371285270341822104, 371285270445083778, 371285270621911020, 371285270726803654, 371285270876583384, 371285271027572142]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494143713991986, 362494246248192323⟩, ⟨(-746917666803279753), (-741199576596974923)⟩, true⟩

def words08 : List Nat := [371285271177238419, 371285271180100532, 371285271247348421, 371285271349977465, 371285271495874387, 371285271547638136, 371285271598361131, 371285271650044319, 371285271797940491, 371285271909867361]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485082016153766, 362485184576183910⟩, ⟨1596121223393571, 7316344841361869⟩, true⟩

def words09 : List Nat := [371285272167148067, 371285272425631081, 371285272650952033, 371285272702155461, 371285272797308057, 371285272893843125, 371285273117868540, 371285273147401574, 371285273149556215, 371285273151787317]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk825B
