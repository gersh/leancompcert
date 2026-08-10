import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk638A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362505673942924477, 362505733914270771⟩, ⟨(-1297970105372786857), (-1295385773898911833)⟩, true⟩

def state01 : KState := ⟨⟨362501725830123840, 362501785821040896⟩, ⟨(-1046098358238592274), (-1043512778049925040)⟩, true⟩

def words00 : List Nat := [371285430672915952, 371285430779960684, 371285431132205230, 371285431485551228, 371285431850288025, 371285431922778267, 371285431993732460, 371285432065447595, 371285432382122256, 371285432640898759]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 63800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 63800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483882707366581, 362483942717808650⟩, ⟨92609642882941367, 95196469064744317⟩, true⟩

def words01 : List Nat := [371285433023971153, 371285433407926401, 371285433780817524, 371285433826900467, 371285433946568756, 371285434067324930, 371285434347507159, 371285434377166152, 371285434378831975, 371285434357875475]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 63810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 63800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362505931239860505, 362505991269736138⟩, ⟨(-1314596195490112450), (-1312008128960849754)⟩, true⟩

def words02 : List Nat := [371285434490876712, 371285434561947593, 371285434877830088, 371285435194613619, 371285435437388307, 371285435513570155, 371285435810606825, 371285436108761478, 371285436541974587, 371285436866249418]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 63820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 63800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496565868710365, 362496625918402089⟩, ⟨(-716766688711176167), (-714177357225599613)⟩, true⟩

def words03 : List Nat := [371285437188930594, 371285437512353803, 371285437863203772, 371285438092760288, 371285438342566463, 371285438593171945, 371285438818473611, 371285438820644428, 371285438926950016, 371285439104955784]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 63830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 63800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486508038423262, 362486568107427753⟩, ⟨(-74576074026451400), (-71985509511810712)⟩, true⟩

def words04 : List Nat := [371285439527286894, 371285439647195813, 371285439768294528, 371285439890110326, 371285440087689871, 371285440163156386, 371285440338499681, 371285440514716843, 371285440689211076, 371285440709117440]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 63840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 63800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk638A
