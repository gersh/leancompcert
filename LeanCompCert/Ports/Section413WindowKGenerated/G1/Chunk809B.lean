import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk809A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk809B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk809A

def state06 : KState := ⟨⟨362506658439177835, 362506756815075357⟩, ⟨(-1753290915516365929), (-1747912883061230193)⟩, true⟩

def words05 : List Nat := [371285165619421628, 371285165749175338, 371285166029964260, 371285166155530862, 371285166241576375, 371285166328409712, 371285166553588067, 371285166710238900, 371285166978818855, 371285167248703138]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 80950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 80900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362496611055604393, 362496709456774317⟩, ⟨(-939794888809612117), (-934414810169867717)⟩, true⟩

def words06 : List Nat := [371285167517529014, 371285167660477880, 371285167954947449, 371285168250879155, 371285168592354138, 371285168731405509, 371285168870894484, 371285169011353867, 371285169194097611, 371285169339816766]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 80960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 80900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480415111503776, 362480513537879826⟩, ⟨371687250199478118, 377069369908363590⟩, true⟩

def words07 : List Nat := [371285169521101274, 371285169703480459, 371285169885117291, 371285169887918908, 371285169866190207, 371285169869439394, 371285169972048532, 371285169974856274, 371285169919375587, 371285169864996502]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 80970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 80900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491784157491707, 362491882608977817⟩, ⟨(-549039590975973081), (-543655437726692069)⟩, true⟩

def words08 : List Nat := [371285169881424687, 371285169904489298, 371285169966932914, 371285170030505291, 371285170068025278, 371285170070827191, 371285169904926015, 371285169881335904, 371285169981765472, 371285170067612398]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 80900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483943674300573, 362484042151349207⟩, ⟨86011970200821028, 91398193882330216⟩, true⟩

def words09 : List Nat := [371285170152297049, 371285170237946108, 371285170379346881, 371285170445679858, 371285170536029196, 371285170627424477, 371285170681231539, 371285170684034079, 371285170534505423, 371285170524113187]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 80990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 80900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 80900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk809B
