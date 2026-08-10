import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk602A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362508529508504006, 362508582658615801⟩, ⟨(-1409124756214095781), (-1406963469345213181)⟩, true⟩

def state01 : KState := ⟨⟨362485756105132601, 362485809273632257⟩, ⟨(-38114303738107324), (-35951909826355270)⟩, true⟩

def words00 : List Nat := [371285211950980556, 371285212032369075, 371285212192294178, 371285212353234158, 371285212596163844, 371285212598202404, 371285212473373396, 371285212278745188, 371285212162666419, 371285212174932247]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491583183758055, 362491636370590966⟩, ⟨(-388917426697893474), (-386753928846532562)⟩, true⟩

def words01 : List Nat := [371285212386878797, 371285212599626089, 371285212810821333, 371285212927534854, 371285213126591566, 371285213326679207, 371285213801845358, 371285213909934925, 371285214018123309, 371285214127040601]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494758614644015, 362494811819758149⟩, ⟨(-580120606099056088), (-577956007259738198)⟩, true⟩

def words02 : List Nat := [371285214348835996, 371285214434129874, 371285214794681135, 371285215156078961, 371285215448679927, 371285215450719162, 371285215539915429, 371285215706829933, 371285216001483661, 371285216162915996]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483244507505271, 362483297731200617⟩, ⟨113449526809029878, 115615244889654766⟩, true⟩

def words03 : List Nat := [371285216291345349, 371285216420472834, 371285216695531281, 371285216834189002, 371285216988132386, 371285217142824149, 371285217256359798, 371285217258399477, 371285217004280044, 371285216974973686]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478606101267942, 362478659343153720⟩, ⟨392976518696157219, 395143332663437895⟩, true⟩

def words04 : List Nat := [371285217154272878, 371285217203120863, 371285217247981031, 371285217293509237, 371285217421206161, 371285217423474887, 371285217542196833, 371285217673151187, 371285217736602444, 371285217738716599]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk602A
