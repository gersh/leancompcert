import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk765A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488754895366680, 362488842348999005⟩, ⟨(-282841323362190815), (-278323447690324027)⟩, true⟩

def state01 : KState := ⟨⟨362485877803292861, 362485965280417172⟩, ⟨(-62721304415378884), (-58201631483243784)⟩, true⟩

def words00 : List Nat := [371285204393162181, 371285204420923080, 371285204422928139, 371285204417446931, 371285204410953519, 371285204403153397, 371285204400884298, 371285204487043201, 371285204571438295, 371285204584158030]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 76500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 76500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501725487993986, 362501812988981805⟩, ⟨(-1275295954914111903), (-1270774456065724801)⟩, true⟩

def words01 : List Nat := [371285204766570671, 371285204950384242, 371285205259199347, 371285205365083889, 371285205443059571, 371285205521852502, 371285205628770621, 371285205678098288, 371285205896919169, 371285206116932751]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 76510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 76500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488284384015012, 362488371908774892⟩, ⟨(-246760515594687299), (-242237197583031115)⟩, true⟩

def words02 : List Nat := [371285206325848682, 371285206328486078, 371285206428363512, 371285206550219626, 371285206722681301, 371285206725319121, 371285206692542234, 371285206628351566, 371285206647729158, 371285206692096905]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 76520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 76500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485272339273542, 362485359887793527⟩, ⟨(-16251899544356225), (-11726763052010143)⟩, true⟩

def words03 : List Nat := [371285206753216605, 371285206815349717, 371285206859484494, 371285206862129515, 371285206731472516, 371285206654281477, 371285206665850163, 371285206669968525, 371285206673943420, 371285206678885204]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 76530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 76500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492598506824531, 362492686078939056⟩, ⟨(-576964446051449170), (-572437503513142246)⟩, true⟩

def words04 : List Nat := [371285206853240802, 371285206943413797, 371285207203029466, 371285207463768312, 371285207681439870, 371285207684078007, 371285207791850732, 371285207912779081, 371285208120574264, 371285208220994508]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 76540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 76500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk765A
