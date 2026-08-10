import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk986A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494420158923269, 362494568309308773⟩, ⟨(-918734856786607767), (-908872586285235349)⟩, true⟩

def state01 : KState := ⟨⟨362484867911058694, 362485016092738326⟩, ⟨23154225246240754, 33019581505442950⟩, true⟩

def words00 : List Nat := [371285350715070655, 371285350718594397, 371285350812092763, 371285350908571254, 371285351000448373, 371285351003912916, 371285350977560439, 371285350952249663, 371285350939011057, 371285350942971624]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 98600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 98600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476371078255557, 362476519291072093⟩, ⟨861103629961317154, 870972056792993154⟩, true⟩

def words01 : List Nat := [371285351024172177, 371285351110144869, 371285351195145814, 371285351198609674, 371285351146394481, 371285351096391124, 371285351055138876, 371285351058619440, 371285350973366146, 371285350887673118]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 98610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 98600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485440316016887, 362485588559874616⟩, ⟨(-33330638059247832), (-23459149784948022)⟩, true⟩

def words02 : List Nat := [371285350813765074, 371285350817618758, 371285350781912069, 371285350785203737, 371285350787363118, 371285350773511637, 371285350666387812, 371285350663862831, 371285350706181937, 371285350712242686]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 98620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 98600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486494907226176, 362486643182691668⟩, ⟨(-137335072084796517), (-127460466181025899)⟩, true⟩

def words03 : List Nat := [371285350716614374, 371285350722148649, 371285350814085908, 371285350865500651, 371285350946491384, 371285351028777483, 371285351070821089, 371285351074285867, 371285351000022342, 371285351017504971]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 98630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 98600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485970741610316, 362486119047934956⟩, ⟨(-85593743611854505), (-75716093605240269)⟩, true⟩

def words04 : List Nat := [371285351135761965, 371285351164188382, 371285351188836191, 371285351214706694, 371285351268972402, 371285351279210813, 371285351361848335, 371285351445958262, 371285351521853577, 371285351533225473]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 98640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 98600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk986A
