import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk634A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476325438446563, 362476384630912086⟩, ⟨569682855803712554, 572217650216037430⟩, true⟩

def state01 : KState := ⟨⟨362493910302344516, 362493969514092509⟩, ⟨(-545291859504509072), (-542755842484424814)⟩, true⟩

def words00 : List Nat := [371285410025531250, 371285410027904891, 371285409959706707, 371285409995727973, 371285409997410717, 371285409989208675, 371285409781156553, 371285409788887454, 371285410044225417, 371285410181445423]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 63400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 63400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491666214306338, 362491725445680544⟩, ⟨(-402990324459530836), (-400453062841461584)⟩, true⟩

def words01 : List Nat := [371285410297360330, 371285410413977273, 371285410632565899, 371285410762753874, 371285410903968288, 371285411046012223, 371285411186456248, 371285411188612075, 371285411140517135, 371285411242769183]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 63410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 63400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476659323920154, 362476718574483360⟩, ⟨548889166759036239, 551427645442609551⟩, true⟩

def words02 : List Nat := [371285411592463445, 371285411686687031, 371285411762868761, 371285411839788269, 371285411949257486, 371285411984304942, 371285412008022842, 371285412032560030, 371285412055548158, 371285412057779003]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 63420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 63400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362507531893060878, 362507591163127009⟩, ⟨(-1409493595196318638), (-1406953879345784498)⟩, true⟩

def words03 : List Nat := [371285412010266595, 371285412100965633, 371285412411664085, 371285412560970842, 371285412671409253, 371285412782495750, 371285412996846173, 371285413100289579, 371285413451343051, 371285413803385741]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 63430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 63400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493378544357899, 362493437833912070⟩, ⟨(-511594764582515567), (-509053812315120517)⟩, true⟩

def words04 : List Nat := [371285414110385961, 371285414112541667, 371285414311007269, 371285414536313942, 371285414835990222, 371285414838146091, 371285414806872488, 371285414775576954, 371285414918700618, 371285415047631080]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 63440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 63400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk634A
