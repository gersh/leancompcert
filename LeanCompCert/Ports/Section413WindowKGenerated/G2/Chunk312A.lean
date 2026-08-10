import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk312A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598772725115632, 360598778599641704⟩, ⟨(-496471249320935050), (-496347303429096856)⟩, true⟩

def state01 : KState := ⟨⟨360576014640098306, 360576020518527058⟩, ⟨213643725437149314, 213767793112568888⟩, true⟩

def words00 : List Nat := [360582871648372114, 360582871730157297, 360582871730530317, 360582871288897054, 360582870847224171, 360582870051435615, 360582870190818030, 360582870340391696, 360582870340761403, 360582869855057420]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 31200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 31200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568682757552254, 360568688639905187⟩, ⟨442275597652827512, 442399787820794108⟩, true⟩

def words01 : List Nat := [360582869656050428, 360582869676621437, 360582869676964520, 360582869288794396, 360582867876798650, 360582865584312326, 360582863291894624, 360582860965930244, 360582859490162542, 360582859036696372]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 31210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 31200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360537781058300924, 360537786944607854⟩, ⟨1407083239650482647, 1407207553281920391⟩, true⟩

def words02 : List Nat := [360582858583195693, 360582857607815131, 360582855972200105, 360582855358721022, 360582854745171928, 360582853863091317, 360582852696149190, 360582850731300732, 360582848766501702, 360582846424379930]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 31220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 31200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360534077806584846, 360534083696801467⟩, ⟨1522971978424425200, 1523096414174962080⟩, true⟩

def words03 : List Nat := [360582844981935213, 360582844561213837, 360582844140474422, 360582843071147213, 360582842448977859, 360582841567632552, 360582840825748066, 360582840826163371, 360582839943821578, 360582838383554827]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 31230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 31200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360613175211240869, 360613181105380075⟩, ⟨(-948539134624396907), (-948414576312755105)⟩, true⟩

def words04 : List Nat := [360582836823297108, 360582835236569785, 360582834315258010, 360582834188889814, 360582834062497200, 360582833058748694, 360582831733128599, 360582831428275646, 360582831838507721, 360582832810083517]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 31240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 31200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk312A
