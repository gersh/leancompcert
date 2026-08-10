import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk840A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569600286811945, 360569646420192563⟩, ⟨1073722336144458338, 1076339407983760618⟩, true⟩

def state01 : KState := ⟨⟨360559593740583815, 360559639885309952⟩, ⟨1914331293687186130, 1916949318607348668⟩, true⟩

def words00 : List Nat := [360582459833007377, 360582459797607100, 360582459661982005, 360582459455560828, 360582459248948183, 360582458986135229, 360582458814400793, 360582458569988538, 360582458325451090, 360582457994089947]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 84000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 84000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360593887686735099, 360593933842845103⟩, ⟨(-966858072871754307), (-964239091537050005)⟩, true⟩

def words01 : List Nat := [360582457723456182, 360582457594746324, 360582457465686368, 360582457426330752, 360582457427453347, 360582457319427958, 360582457243490569, 360582457399673314, 360582457537246056, 360582457675083032]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 84010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 84000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575410301512054, 360575456469116129⟩, ⟨585631765113006183, 588251712237665713⟩, true⟩

def words02 : List Nat := [360582457703774936, 360582457704981463, 360582457689957143, 360582457736241393, 360582457745376311, 360582457746582405, 360582457614370473, 360582457390824740, 360582457167038820, 360582456965513103]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 84020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 84000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360540452625288485, 360540498804245559⟩, ⟨3523341929689249592, 3525962830863555462⟩, true⟩

def words03 : List Nat := [360582456883182306, 360582456848730432, 360582456814152058, 360582456708649778, 360582456461575848, 360582456118338655, 360582455774757089, 360582455493774652, 360582455071278843, 360582454573294388]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 84030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 84000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360562811361512000, 360562857551870788⟩, ⟨1644243744202449689, 1646865603630631805⟩, true⟩

def words04 : List Nat := [360582454075040491, 360582453663170974, 360582453378260585, 360582453208241366, 360582453038137778, 360582452745863191, 360582452311996032, 360582452019931602, 360582451727533232, 360582451431747417]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 84040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 84000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk840A
