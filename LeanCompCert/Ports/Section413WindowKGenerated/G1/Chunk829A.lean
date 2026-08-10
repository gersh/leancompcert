import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk829A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488728977087353, 362488832312270150⟩, ⟨(-298833974448595414), (-293049606803759892)⟩, true⟩

def state01 : KState := ⟨⟨362486197566542370, 362486300927474838⟩, ⟨(-88938262085548791), (-83151759663712751)⟩, true⟩

def words00 : List Nat := [371285297457311525, 371285297471703225, 371285297630447377, 371285297790384468, 371285297926130611, 371285297929004668, 371285297884379329, 371285297901725627, 371285298008570532, 371285298023642250]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491295392149234, 362491398779285367⟩, ⟨(-511623109470570799), (-505834434369789737)⟩, true⟩

def words01 : List Nat := [371285298025792808, 371285298028657696, 371285298175555345, 371285298269352145, 371285298347902870, 371285298427495119, 371285298493296345, 371285298496190425, 371285298505143149, 371285298582298238]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485396302773199, 362485499715551663⟩, ⟨(-22388512559384532), (-16597711062385492)⟩, true⟩

def words02 : List Nat := [371285298780912172, 371285298859894234, 371285298934530138, 371285299010108899, 371285299120091061, 371285299173931755, 371285299323355065, 371285299473974172, 371285299571359219, 371285299576748775]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362507160767604939, 362507264206336571⟩, ⟨(-1827433233718744343), (-1821640279795038551)⟩, true⟩

def words03 : List Nat := [371285299712870940, 371285299850449389, 371285300115562274, 371285300187787017, 371285300233938321, 371285300281038114, 371285300463397596, 371285300585958479, 371285300852721912, 371285301120772194]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489720295913072, 362489823760615323⟩, ⟨(-380896645279079497), (-375101537226413049)⟩, true⟩

def words04 : List Nat := [371285301387431193, 371285301479213031, 371285301572257064, 371285301666829150, 371285301795216934, 371285301798092978, 371285301753237935, 371285301704745639, 371285301737535694, 371285301795392163]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk829A
