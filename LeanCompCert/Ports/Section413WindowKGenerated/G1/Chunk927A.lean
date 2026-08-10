import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk927A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493981083266749, 362494111412919990⟩, ⟨(-842059641367696994), (-833902502948331680)⟩, true⟩

def state01 : KState := ⟨⟨362481669992928295, 362481800351499988⟩, ⟨299203057844717172, 307362877152939576⟩, true⟩

def words00 : List Nat := [371285115888329457, 371285115891571635, 371285115827061561, 371285115762469078, 371285115696589657, 371285115667689030, 371285115605210583, 371285115634612246, 371285115663396109, 371285115666753499]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 92700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 92700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492363475575844, 362492493863491834⟩, ⟨(-692239832082586156), (-684077292118714860)⟩, true⟩

def words01 : List Nat := [371285115704599108, 371285115779913900, 371285115906545546, 371285115909788255, 371285115893070810, 371285115848671760, 371285115871364336, 371285115895221267, 371285115977007601, 371285116060274454]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 92710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 92700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487103175902686, 362487233593083475⟩, ⟨(-204472634873356375), (-196307381325551309)⟩, true⟩

def words02 : List Nat := [371285116143144720, 371285116146446124, 371285116261802872, 371285116380369277, 371285116532581081, 371285116545312435, 371285116557773401, 371285116571336618, 371285116611235140, 371285116637789932]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 92720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 92700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481096336953922, 362481226783306072⟩, ⟨352610127357016045, 360778086107677553⟩, true⟩

def words03 : List Nat := [371285116760316352, 371285116884131085, 371285117006616747, 371285117009860400, 371285116986949913, 371285116976572846, 371285117066193006, 371285117069436978, 371285117031755471, 371285116993421532]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 92730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 92700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488095622771879, 362488226098175265⟩, ⟨(-296543135879104443), (-288372482771098385)⟩, true⟩

def words04 : List Nat := [371285116971056914, 371285116974653968, 371285116998628340, 371285117037262829, 371285117051322171, 371285117054566715, 371285116927855669, 371285116903967872, 371285116957472268, 371285116994416049]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 92740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 92700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk927A
