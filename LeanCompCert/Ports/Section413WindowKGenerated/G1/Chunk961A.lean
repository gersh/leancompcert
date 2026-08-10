import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk961A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483764336196085, 362483904792185801⟩, ⟨122015273735125127, 131128450224249791⟩, true⟩

def state01 : KState := ⟨⟨362485138879662897, 362485279365839803⟩, ⟨(-10069206591501715), (-953128957145415)⟩, true⟩

def words00 : List Nat := [371285269334081865, 371285269351974624, 371285269413286113, 371285269475960664, 371285269515695941, 371285269519069092, 371285269441520118, 371285269420875801, 371285269445226300, 371285269448879652]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491996545033968, 362492137061956791⟩, ⟨(-669199415304849095), (-660080382529768637)⟩, true⟩

def words01 : List Nat := [371285269451422530, 371285269447441928, 371285269529648449, 371285269571729794, 371285269638316745, 371285269706163107, 371285269754209119, 371285269757612147, 371285269804453841, 371285269880149176]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487739681363992, 362487880228304266⟩, ⟨(-259981438439131941), (-250859520228278427)⟩, true⟩

def words02 : List Nat := [371285270033490817, 371285270084530237, 371285270133869938, 371285270184380774, 371285270265682088, 371285270297635224, 371285270418179580, 371285270540142965, 371285270638626412, 371285270669262664]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362503379801011381, 362503520378440708⟩, ⟨(-1763573378039493406), (-1754448528766510780)⟩, true⟩

def words03 : List Nat := [371285270737953498, 371285270808313859, 371285270975878307, 371285271014315258, 371285271037684815, 371285271062113310, 371285271193461242, 371285271290001417, 371285271482105238, 371285271675714853]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493184132639285, 362493324740443076⟩, ⟨(-783346088381600832), (-774218318751269202)⟩, true⟩

def words04 : List Nat := [371285271870562375, 371285271937758528, 371285272100878682, 371285272265790805, 371285272414539555, 371285272420001635, 371285272424951918, 371285272431003787, 371285272543988562, 371285272631585641]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk961A
