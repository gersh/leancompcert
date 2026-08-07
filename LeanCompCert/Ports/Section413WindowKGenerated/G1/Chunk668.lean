import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk668

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362503263497949008, 362503329479252813⟩, ⟨(-1193473571895406980), (-1190496715514743200)⟩, true⟩

def state01 : KState := ⟨⟨362484887949909257, 362484953951784542⟩, ⟨34028424408791216, 37006655069864898⟩, true⟩

def words00 : List Nat := [371285508161817016, 371285508164095657, 371285508177603430, 371285508243851539, 371285508364201219, 371285508366479963, 371285508188528393, 371285508004985252, 371285507858100044, 371285507860706408]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 66800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 66800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477628140708708, 362477694163081772⟩, ⟨519161824953980135, 522141425174060405⟩, true⟩

def words01 : List Nat := [371285508038975027, 371285508226435140, 371285508413424083, 371285508415718654, 371285508401816738, 371285508380798245, 371285508539588252, 371285508541867572, 371285508426311071, 371285508311917062]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 66810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 66800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481884933373344, 362481950976159123⟩, ⟨234781695907921630, 237762660210509118⟩, true⟩

def words02 : List Nat := [371285508303195973, 371285508335862265, 371285508531162338, 371285508727401006, 371285508855360293, 371285508857640080, 371285508687118047, 371285508660493307, 371285508697278678, 371285508699639754]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 66820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 66800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484119629382097, 362484185692964451⟩, ⟨85427632416086935, 88409986657614495⟩, true⟩

def words03 : List Nat := [371285508648109491, 371285508597716184, 371285508592090734, 371285508594627788, 371285508578164415, 371285508605997102, 371285508633363380, 371285508635646855, 371285508420660923, 371285508403716361]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 66830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 66800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476227282915759, 362476293366842958⟩, ⟨613025472556335460, 616009186753299230⟩, true⟩

def words04 : List Nat := [371285508589135272, 371285508591420465, 371285508565656847, 371285508498178566, 371285508429844503, 371285508404659264, 371285508293844791, 371285508250721906, 371285508206798347, 371285508163952208]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 66840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 66800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk668
