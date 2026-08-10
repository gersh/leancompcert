import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk804A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360565800559598435, 360565842679797767⟩, ⟨1310571791471675807, 1312858923282705205⟩, true⟩

def state01 : KState := ⟨⟨360574395939894961, 360574438070948312⟩, ⟨619398567566023710, 621686572093540390⟩, true⟩

def words00 : List Nat := [360582171568718761, 360582171373162361, 360582171181394844, 360582170912437804, 360582170643304612, 360582170289591465, 360582170014235363, 360582169893575785, 360582169772808022, 360582169529375045]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 80400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 80400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360593950058322014, 360593992200221791⟩, ⟨(-953059841791981198), (-950770965048311136)⟩, true⟩

def words01 : List Nat := [360582169462972249, 360582169493055617, 360582169635510517, 360582169685919305, 360582169686990326, 360582169606989432, 360582169526751570, 360582169482510605, 360582169630452869, 360582169778652198]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 80410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 80400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574234089775494, 360574276242645126⟩, ⟨632452995205290288, 634742754199065244⟩, true⟩

def words02 : List Nat := [360582169809926342, 360582169811076914, 360582169728609710, 360582169642584861, 360582169556246453, 360582169429482297, 360582169148304798, 360582168750178859, 360582168351842537, 360582168108294748]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 80420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 80400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360539685495357720, 360539727659054480⟩, ⟨3411385174618392590, 3413675804493539916⟩, true⟩

def words03 : List Nat := [360582168011111150, 360582167891417276, 360582167771603984, 360582167569993109, 360582167251211381, 360582166894182999, 360582166536841971, 360582166175848469, 360582165726517673, 360582165200134708]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 80430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 80400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573928731953792, 360573970906517570⟩, ⟨656656530308399011, 658948034378248081⟩, true⟩

def words04 : List Nat := [360582164673504035, 360582164274505359, 360582163971190014, 360582163644048771, 360582163316798443, 360582162862117679, 360582162413081945, 360582162118694825, 360582161823977204, 360582161683824945]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 80440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 80400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk804A
