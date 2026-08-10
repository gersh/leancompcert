import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk905A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497835582843992, 362497959569036913⟩, ⟨(-1169585484555843300), (-1162009438036694822)⟩, true⟩

def state01 : KState := ⟨⟨362485984263599408, 362486108278340545⟩, ⟨(-97029239058180559), (-89450608782837045)⟩, true⟩

def words00 : List Nat := [371285119961086269, 371285119964246470, 371285119994920489, 371285120038033986, 371285120093580573, 371285120096754949, 371285120045144862, 371285119994515362, 371285119979360739, 371285119993946573]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 90500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 90500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362472677506545939, 362472801549726019⟩, ⟨1107505087699005143, 1115086292128235515⟩, true⟩

def words01 : List Nat := [371285120129005978, 371285120265389936, 371285120400011156, 371285120403170202, 371285120398688865, 371285120412830455, 371285120463737441, 371285120466896630, 371285120355367924, 371285120222860445]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 90510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 90500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489587819758489, 362489711891228671⟩, ⟨(-423284066995886275), (-415700301608342741)⟩, true⟩

def words02 : List Nat := [371285120088916653, 371285120068865498, 371285120047158632, 371285120099679012, 371285120119293047, 371285120122452505, 371285119979140173, 371285119959482650, 371285120036597601, 371285120090612216]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 90520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 90500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362497566784617558, 362497690884879598⟩, ⟨(-1145665688058866079), (-1138079315997421343)⟩, true⟩

def words03 : List Nat := [371285120122194370, 371285120154764554, 371285120308006858, 371285120408049868, 371285120534403388, 371285120661988285, 371285120787448609, 371285120833689401, 371285120974667694, 371285121117415163]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 90530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 90500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491048450216945, 362491172578595156⟩, ⟨(-555458549351798988), (-547869631502209750)⟩, true⟩

def words04 : List Nat := [371285121320685651, 371285121400254289, 371285121478928568, 371285121558710088, 371285121644021624, 371285121669673299, 371285121815891789, 371285121963365038, 371285122110035002, 371285122180129074]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 90540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 90500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk905A
