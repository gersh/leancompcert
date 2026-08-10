import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk756A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485182703036175, 362485268033001970⟩, ⟨(-8775013247381922), (-4418644781550886)⟩, true⟩

def state01 : KState := ⟨⟨362466568474345586, 362466653827464655⟩, ⟨1398559233124878658, 1402917352100345422⟩, true⟩

def words00 : List Nat := [371285209670923975, 371285209673526863, 371285209544177377, 371285209373918799, 371285209202690230, 371285209085692547, 371285208880211734, 371285208746690146, 371285208612276222, 371285208480977423]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 75600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 75600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502126782983169, 362502212159605657⟩, ⟨(-1290174162566360255), (-1285814266377867853)⟩, true⟩

def words01 : List Nat := [371285208237346837, 371285208169824848, 371285208188389165, 371285208191055759, 371285208183950105, 371285208149093992, 371285208250161503, 371285208303171579, 371285208529796548, 371285208757556255]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 75610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 75600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486738344890565, 362486823745018184⟩, ⟨(-126482232592600997), (-122120558826766207)⟩, true⟩

def words02 : List Nat := [371285208958202308, 371285208960805805, 371285209042664038, 371285209160252663, 371285209284558071, 371285209287161628, 371285209178607461, 371285209072651265, 371285209031498968, 371285209055818957]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 75620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 75600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362478850637487343, 362478936061085637⟩, ⟨470158459143934992, 474521908114139122⟩, true⟩

def words03 : List Nat := [371285209226185711, 371285209397644178, 371285209545404364, 371285209548020708, 371285209528460251, 371285209518256352, 371285209639272559, 371285209641877139, 371285209566615801, 371285209486629188]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 75630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 75600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479269060492350, 362479354507436137⟩, ⟨438593437472407862, 442958652413211272⟩, true⟩

def words04 : List Nat := [371285209497169075, 371285209528515488, 371285209709465540, 371285209891446932, 371285210033187902, 371285210035792433, 371285209964806704, 371285209919242512, 371285209873564858, 371285209876271738]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 75640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 75600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk756A
