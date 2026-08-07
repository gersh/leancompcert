import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk555

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482515221299647, 362482560105126591⟩, ⟨131782959954358136, 133465758030592246⟩, true⟩

def state01 : KState := ⟨⟨362479931528912366, 362479976429397830⟩, ⟨275182517036789505, 276866239747837281⟩, true⟩

def words00 : List Nat := [371284965132277435, 371284965134145118, 371284964984115205, 371284964771201240, 371284964557559669, 371284964376311818, 371284964104514618, 371284964107025555, 371284964109636019, 371284964111612708]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 55500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 55500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497919467604690, 362497964384979211⟩, ⟨(-723378192753729508), (-721693532445867090)⟩, true⟩

def words01 : List Nat := [371284964257170668, 371284964493577193, 371284964996121454, 371284965123935714, 371284965199264743, 371284965275155250, 371284965370311476, 371284965372374502, 371284965580036351, 371284965816285458]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 55510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 55500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490889033894880, 362490933968140614⟩, ⟨(-333050696191244525), (-331365099106683823)⟩, true⟩

def words02 : List Nat := [371284966068919047, 371284966075353251, 371284966297283499, 371284966520185324, 371284966837630100, 371284966839498826, 371284966725173106, 371284966592886679, 371284966649239984, 371284966758850188]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 55520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 55500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362465528131865116, 362465573082942778⟩, ⟨1075419489670561036, 1077106021518773090⟩, true⟩

def words03 : List Nat := [371284967002438259, 371284967246738125, 371284967480357270, 371284967482226196, 371284967284022789, 371284967143426379, 371284967018317384, 371284967020218976, 371284966768567806, 371284966421464903]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 55530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 55500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483528058512527, 362483573026303506⟩, ⟨75662190176086600, 77349650368000594⟩, true⟩

def words04 : List Nat := [371284966073561436, 371284966050110424, 371284965950228176, 371284966038995584, 371284966040469443, 371284966032261170, 371284965591894673, 371284965476088983, 371284965457303185, 371284965459253426]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 55540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 55500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk555
