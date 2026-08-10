import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk929A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496287805159485, 362496418719425086⟩, ⟨(-1057370288103543249), (-1049158897578300355)⟩, true⟩

def state01 : KState := ⟨⟨362490531282558625, 362490662226132574⟩, ⟨(-522607072304530263), (-514392958887742447)⟩, true⟩

def words00 : List Nat := [371285125541195735, 371285125544445573, 371285125575451503, 371285125642960809, 371285125719833016, 371285125723106769, 371285125713916949, 371285125696658180, 371285125757461962, 371285125820767357]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 92900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 92900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478337987598826, 362478468960497068⟩, ⟨610343008967454582, 618559847054037504⟩, true⟩

def words01 : List Nat := [371285125910456638, 371285126001461247, 371285126091034136, 371285126094284626, 371285126029321868, 371285126001436538, 371285125999244671, 371285126002552016, 371285125935974462, 371285125868020250]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 92910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 92900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487364093360136, 362487495095359557⟩, ⟨(-228362103915572412), (-220142561603366266)⟩, true⟩

def words02 : List Nat := [371285125842778428, 371285125846370883, 371285125937677967, 371285126033706343, 371285126094184267, 371285126097435434, 371285126047270983, 371285126082963297, 371285126184626925, 371285126213483721]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 92920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 92900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482557806201916, 362482688837807289⟩, ⟨218363752273829353, 226586046021751021⟩, true⟩

def words03 : List Nat := [371285126241117703, 371285126269881487, 371285126410088726, 371285126494718193, 371285126613457696, 371285126733469943, 371285126851650939, 371285126854904752, 371285126842035803, 371285126819795903]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 92930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 92900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481743236574628, 362481874297149421⟩, ⟨294070661135867802, 302295647450563180⟩, true⟩

def words04 : List Nat := [371285126885323555, 371285126888575079, 371285126826291988, 371285126756667897, 371285126685756302, 371285126637765508, 371285126546228784, 371285126543467386, 371285126539629004, 371285126536498002]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 92940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 92900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk929A
