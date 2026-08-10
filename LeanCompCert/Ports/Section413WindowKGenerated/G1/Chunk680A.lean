import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk680A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502026102841414, 362502094571246549⟩, ⟨(-1135072954084396174), (-1131928462113998396)⟩, true⟩

def state01 : KState := ⟨⟨362489004612199519, 362489073101538617⟩, ⟨(-249581650676454137), (-246435735087013403)⟩, true⟩

def words00 : List Nat := [371285449049739200, 371285449103913551, 371285449300235612, 371285449497748694, 371285449676965375, 371285449679289988, 371285449608739841, 371285449539117648, 371285449576831767, 371285449632760229]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 68000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 68000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362470529630457980, 362470598140736582⟩, ⟨1007060127734457719, 1010207467523365655⟩, true⟩

def words01 : List Nat := [371285449843697260, 371285450055594474, 371285450216831885, 371285450219157322, 371285450137174409, 371285450094905006, 371285450143355034, 371285450145679137, 371285449980532323, 371285449764781325]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 68010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 68000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491152238416691, 362491220769480806⟩, ⟨(-395739412613977084), (-392590658886048160)⟩, true⟩

def words02 : List Nat := [371285449548018891, 371285449528886577, 371285449487631799, 371285449576745371, 371285449628862194, 371285449631227879, 371285449614565584, 371285449696915230, 371285449920993884, 371285450008226583]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 68020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 68000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484996191617836, 362485064743938703⟩, ⟨23109463983920045, 26259663908791915⟩, true⟩

def words03 : List Nat := [371285450094257445, 371285450181087723, 371285450357473251, 371285450474292065, 371285450599579897, 371285450725722607, 371285450851260966, 371285450853585726, 371285450691131638, 371285450688440596]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 68030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 68000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479764788190763, 362479833361200116⟩, ⟨379132286480842552, 382283894160697138⟩, true⟩

def words04 : List Nat := [371285450894480202, 371285450900733638, 371285450902472330, 371285450887389718, 371285450911397684, 371285450913976758, 371285450935684027, 371285450993541635, 371285451050107977, 371285451052517687]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 68040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 68000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk680A
