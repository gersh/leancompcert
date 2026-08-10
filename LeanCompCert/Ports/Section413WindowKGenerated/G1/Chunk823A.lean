import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk823A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480267865028120, 362480369652824227⟩, ⟨396905030142483374, 402561582925860846⟩, true⟩

def state01 : KState := ⟨⟨362499859207035246, 362499961020354413⟩, ⟨(-1215524429458107490), (-1209865775997839930)⟩, true⟩

def words00 : List Nat := [371285261075858193, 371285261129886540, 371285261278268747, 371285261427839938, 371285261551136159, 371285261554037641, 371285261701166597, 371285261850995476, 371285262125700008, 371285262307229827]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494363066126777, 362494464905506785⟩, ⟨(-763112300087365857), (-757451501433000093)⟩, true⟩

def words01 : List Nat := [371285262487748063, 371285262669250490, 371285262868443773, 371285263010658807, 371285263177961876, 371285263346342177, 371285263503165376, 371285263506017809, 371285263595973034, 371285263711383378]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480419727489201, 362480521592241002⟩, ⟨384806078389560728, 390468965784572134⟩, true⟩

def words02 : List Nat := [371285263961506837, 371285264015835466, 371285264069474937, 371285264124049147, 371285264197579117, 371285264200722579, 371285264239073024, 371285264280672249, 371285264319347350, 371285264322300332]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499686132129497, 362499788022633634⟩, ⟨(-1201516226553259434), (-1195851218837814534)⟩, true⟩

def words03 : List Nat := [371285264266636465, 371285264267363975, 371285264404498931, 371285264423086925, 371285264425309735, 371285264400271676, 371285264476433543, 371285264508378653, 371285264686698217, 371285264866261501]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362499660166936648, 362499762083252136⟩, ⟨(-1199429778424297583), (-1193762645275748185)⟩, true⟩

def words04 : List Nat := [371285265015473946, 371285265024179708, 371285265157067345, 371285265291458149, 371285265457280543, 371285265524830755, 371285265591429513, 371285265659026456, 371285265872973065, 371285266052295916]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk823A
