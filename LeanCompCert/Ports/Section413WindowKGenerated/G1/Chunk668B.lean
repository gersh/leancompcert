import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk668A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk668B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk668A

def state06 : KState := ⟨⟨362491621312056286, 362491687416551070⟩, ⟨(-416098073480459582), (-413112984233636270)⟩, true⟩

def words05 : List Nat := [371285508113218416, 371285508201507731, 371285508511999723, 371285508525235641, 371285508527000516, 371285508504556947, 371285508550077643, 371285508552607865, 371285508637698261, 371285508732651134]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 66850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 66800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474690430346165, 362474756555439706⟩, ⟨715951866699586021, 718938333282974639⟩, true⟩

def words06 : List Nat := [371285508782700349, 371285508784981519, 371285508556859082, 371285508553335652, 371285508592502714, 371285508594784211, 371285508375113044, 371285508158352865, 371285507940702017, 371285507839024019]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 66860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 66800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362471094728171160, 362471160873864005⟩, ⟨956406122760040942, 959393966921427732⟩, true⟩

def words07 : List Nat := [371285507679822782, 371285507563977417, 371285507447333311, 371285507331599390, 371285506973033493, 371285506676423084, 371285506378664104, 371285506304952037, 371285506091222531, 371285505879350271]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 66870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 66800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490776001261889, 362490842167346825⟩, ⟨(-359940088767714349), (-356950880677930855)⟩, true⟩

def words08 : List Nat := [371285505666412950, 371285505639436869, 371285505601835515, 371285505696324610, 371285505755789682, 371285505758072149, 371285505553280530, 371285505555353083, 371285505778668729, 371285505860808159]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 66880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 66800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487900818989957, 362487967005868818⟩, ⟨(-167580770083454798), (-164590170982118204)⟩, true⟩

def words09 : List Nat := [371285505898359670, 371285505936691046, 371285506177205977, 371285506306808650, 371285506452759535, 371285506599607099, 371285506744671645, 371285506746966849, 371285506761345821, 371285506800924466]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 66890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 66800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 66800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk668B
