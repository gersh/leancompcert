import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk578A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362505329522319881, 362505378360932126⟩, ⟨(-1181282272705609205), (-1179375402503433689)⟩, true⟩

def state01 : KState := ⟨⟨362500235418420209, 362500284274605610⟩, ⟨(-886893257711757702), (-884985371688638376)⟩, true⟩

def words00 : List Nat := [371284974648316566, 371284974650266979, 371284974856233252, 371284975110619024, 371284975378500095, 371284975399102535, 371284975417839153, 371284975437243401, 371284975755311582, 371284976022340667]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 57800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 57800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475621380676704, 362475670254439911⟩, ⟨536239966462011290, 538148868745542680⟩, true⟩

def words01 : List Nat := [371284976486189259, 371284976950790889, 371284977359199290, 371284977403559710, 371284977522412865, 371284977642279744, 371284977882913087, 371284977884864282, 371284977726739226, 371284977567977538]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 57810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 57800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484830312957340, 362484879204171375⟩, ⟨3799286286911757, 5709197666259175⟩, true⟩

def words02 : List Nat := [371284977500596323, 371284977502749415, 371284977695665599, 371284977922123397, 371284978099098066, 371284978101051240, 371284977956338419, 371284977847546380, 371284977925956721, 371284977927976775]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 57820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 57800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498886838887533, 362498935747913168⟩, ⟨(-809165680809289621), (-807254739297632271)⟩, true⟩

def words03 : List Nat := [371284977927729763, 371284977900015462, 371284978105721501, 371284978248638529, 371284978457548525, 371284978667184266, 371284978872425039, 371284978874390242, 371284979059105409, 371284979302843103]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 57830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 57800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484593910876721, 362484642837300292⟩, ⟨17588874928541063, 19500822828006091⟩, true⟩

def words04 : List Nat := [371284979668160094, 371284979670112079, 371284979636991209, 371284979606055529, 371284979579927560, 371284979582080073, 371284979631459963, 371284979807219480, 371284979928142659, 371284979930175453]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 57840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 57800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk578A
