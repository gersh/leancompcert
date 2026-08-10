import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk555A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk555B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk555A

def state06 : KState := ⟨⟨362478472905042740, 362478517889890703⟩, ⟨356567385315546174, 358255793106810838⟩, true⟩

def words05 : List Nat := [371284965435585140, 371284965413277785, 371284965656879788, 371284965791642877, 371284965974327775, 371284966157714508, 371284966339691099, 371284966341560761, 371284966092046149, 371284965978319552]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474454971800463, 362474499973305079⟩, ⟨579839169639447028, 581528502960243022⟩, true⟩

def words06 : List Nat := [371284965914282639, 371284965916161270, 371284965657576051, 371284965400330106, 371284965142393182, 371284964984162386, 371284964724464268, 371284964743967382, 371284964763576931, 371284964765512390]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496913024580239, 362496958042986971⟩, ⟨(-668299617534200885), (-666609344877232471)⟩, true⟩

def words07 : List Nat := [371284964663624006, 371284964751009142, 371284964897952786, 371284964899823972, 371284964673163733, 371284964435049241, 371284964238090665, 371284964240151901, 371284964349884309, 371284964567790821]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470580609763005, 362470625645041080⟩, ⟨795299124696630018, 796990335148426554⟩, true⟩

def words08 : List Nat := [371284964759124561, 371284964760995109, 371284964521245292, 371284964402584216, 371284964282955237, 371284964262735020, 371284963811172518, 371284963294025814, 371284962776144725, 371284962582172731]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470110038114435, 362470155090247528⟩, ⟨821544179808173180, 823236327315649016⟩, true⟩

def words09 : List Nat := [371284962325543570, 371284962303280580, 371284962280386562, 371284962228650802, 371284962031496684, 371284961934097229, 371284962013189382, 371284962015060609, 371284961763190319, 371284961499012198]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk555B
