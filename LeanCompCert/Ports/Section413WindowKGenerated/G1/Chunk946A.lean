import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk946A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485502711989718, 362485638652179791⟩, ⟨(-52041724992081500), (-43359139789973376)⟩, true⟩

def state01 : KState := ⟨⟨362489060723306670, 362489196693135791⟩, ⟨(-388629329650385730), (-379943940445603652)⟩, true⟩

def words00 : List Nat := [371285180373726059, 371285180377977537, 371285180492647979, 371285180608636351, 371285180687734458, 371285180691048600, 371285180647223056, 371285180677666013, 371285180793494447, 371285180839372005]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 94600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 94600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485105952594971, 362485241952603512⟩, ⟨(-14421700723977966), (-5733456091676422)⟩, true⟩

def words01 : List Nat := [371285180852308602, 371285180866382285, 371285180990868499, 371285181074138594, 371285181179747900, 371285181286655012, 371285181392897617, 371285181396212292, 371285181353976931, 371285181358696328]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 94610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 94600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487240504335352, 362487376533884042⟩, ⟨(-216353423252936644), (-207662383378249082)⟩, true⟩

def words02 : List Nat := [371285181473364574, 371285181528402386, 371285181582212744, 371285181637189400, 371285181723918688, 371285181771892372, 371285181868790297, 371285181966995164, 371285182063756716, 371285182090378444]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 94620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 94600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490695372554194, 362490831432139442⟩, ⟨(-543301855546382650), (-534607973162862002)⟩, true⟩

def words03 : List Nat := [371285182216629513, 371285182344627932, 371285182484054689, 371285182487369868, 371285182478229484, 371285182453393828, 371285182493516523, 371285182507788293, 371285182569735461, 371285182633276763]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 94630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 94600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479300904277056, 362479436993734428⟩, ⟨535086607446858786, 543783317081865764⟩, true⟩

def words04 : List Nat := [371285182695093959, 371285182698409762, 371285182625152618, 371285182622549724, 371285182624680142, 371285182627997522, 371285182507524677, 371285182366573639, 371285182224245553, 371285182195182731]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 94640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 94600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk946A
