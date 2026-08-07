import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk804

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

def state06 : KState := ⟨⟨360581160034181099, 360581202219733380⟩, ⟨74827472512443742, 77119860659752646⟩, true⟩

def words05 : List Nat := [360582161583067452, 360582161362528459, 360582161141774940, 360582161026995086, 360582161027958432, 360582160997503631, 360582160966928972, 360582160838172342, 360582160717277673, 360582160706691618]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360570637030780821, 360570679227167432⟩, ⟨921494175106928487, 923787435040062909⟩, true⟩

def words06 : List Nat := [360582160736256645, 360582160737407790, 360582160624828049, 360582160435216738, 360582160245447606, 360582159909463104, 360582159650437555, 360582159501489688, 360582159352429788, 360582159125701545]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585369933329638, 360585412140599666⟩, ⟨(-264111848827140912), (-261817713053738044)⟩, true⟩

def words07 : List Nat := [360582158995515075, 360582159008347162, 360582159175012016, 360582159187782610, 360582159188847244, 360582159052472779, 360582158915873687, 360582158895837878, 360582158937207901, 360582158978821685]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575879453356776, 360575921671586073⟩, ⟨499578867872814428, 501873885703562498⟩, true⟩

def words08 : List Nat := [360582158979847632, 360582158937923872, 360582158741697908, 360582158533868632, 360582158325736606, 360582158079352676, 360582157836730196, 360582157474572235, 360582157112202793, 360582156904356648]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360562916281292906, 360562958510386721⟩, ⟨1543081442870455670, 1545377335239104604⟩, true⟩

def words09 : List Nat := [360582156904487419, 360582156982301780, 360582156983345684, 360582156942526080, 360582156782400968, 360582156530750516, 360582156278749905, 360582156141969682, 360582155981626694, 360582155744364847]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk804
