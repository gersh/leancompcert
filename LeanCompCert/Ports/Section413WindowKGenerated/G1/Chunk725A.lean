import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk725A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504157764757491, 362504235985110629⟩, ⟨(-1378371327632795190), (-1374541508848282392)⟩, true⟩

def state01 : KState := ⟨⟨362494832893506208, 362494911136305806⟩, ⟨(-702327323868897686), (-698495877601365056)⟩, true⟩

def words00 : List Nat := [371285277284251094, 371285277286739873, 371285277429546066, 371285277598135242, 371285277780120280, 371285277804291835, 371285277828494123, 371285277853513738, 371285278036271953, 371285278171961068]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 72500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 72500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488561795064086, 362488640060331595⟩, ⟨(-247522555485669782), (-243689479958176202)⟩, true⟩

def words01 : List Nat := [371285278461730059, 371285278752558107, 371285279007254422, 371285279080596679, 371285279210831436, 371285279342266404, 371285279639202924, 371285279702035427, 371285279750235932, 371285279799442223]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 72510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 72500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478718666188501, 362478796953732750⟩, ⟨466419519686096893, 470254210837140745⟩, true⟩

def words02 : List Nat := [371285280007199030, 371285280143254880, 371285280335760122, 371285280529235410, 371285280689206724, 371285280691696246, 371285280598220866, 371285280550601185, 371285280533271119, 371285280535848249]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 72520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 72500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481203512699514, 362481281822920733⟩, ⟨286225396311594148, 290061732335676944⟩, true⟩

def words03 : List Nat := [371285280448336385, 371285280360522612, 371285280371078004, 371285280421620361, 371285280508348569, 371285280596050201, 371285280683585323, 371285280686075434, 371285280520274374, 371285280468252077]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 72530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 72500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473970653436290, 362474048985858944⟩, ⟨810937274725579366, 814775221357864838⟩, true⟩

def words04 : List Nat := [371285280414848803, 371285280414683862, 371285280266530563, 371285280119973432, 371285279972443314, 371285279833768441, 371285279612445488, 371285279581941187, 371285279550592038, 371285279519578557]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 72540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 72500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk725A
