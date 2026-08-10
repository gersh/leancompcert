import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk897A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485627219991597, 362485748940813365⟩, ⟨(-62205761074744615), (-54833826162161167)⟩, true⟩

def state01 : KState := ⟨⟨362475554637042223, 362475676385672854⟩, ⟨841374733326269121, 848749162842802599⟩, true⟩

def words00 : List Nat := [371285137767276464, 371285137770405301, 371285137727086465, 371285137685406047, 371285137642553363, 371285137582282802, 371285137458710913, 371285137450100069, 371285137440465603, 371285137417473577]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 89700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 89700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487528154671430, 362487649931674478⟩, ⟨(-232816941168565397), (-225439966223886255)⟩, true⟩

def words01 : List Nat := [371285137326590422, 371285137342936448, 371285137418213942, 371285137421345679, 371285137356237658, 371285137272467202, 371285137211949289, 371285137215405713, 371285137222308890, 371285137253859654]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 89710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 89700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481800210499537, 362481922015771603⟩, ⟨281074810468482492, 288454321852892722⟩, true⟩

def words02 : List Nat := [371285137282656256, 371285137285786055, 371285137164591397, 371285137111656480, 371285137057212135, 371285137015687446, 371285136928582691, 371285136819715439, 371285136709531609, 371285136707868482]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 89720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 89700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474014312034559, 362474136145482188⟩, ⟨979775158488668425, 987157198214406079⟩, true⟩

def words03 : List Nat := [371285136743229310, 371285136815660224, 371285136863471798, 371285136866602021, 371285136748736862, 371285136658622670, 371285136566863371, 371285136567464704, 371285136456158424, 371285136337127101]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 89730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 89700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473332059100817, 362473453920545341⟩, ⟨1041057921785198544, 1048442474094964552⟩, true⟩

def words04 : List Nat := [371285136216673544, 371285136200064895, 371285136120222655, 371285136120083124, 371285136118928516, 371285136109385528, 371285135964851947, 371285135873396193, 371285135780329183, 371285135730841664]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 89740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 89700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk897A
