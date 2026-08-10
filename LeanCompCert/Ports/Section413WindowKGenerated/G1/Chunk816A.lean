import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk816A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490059197797802, 362490159195883422⟩, ⟨(-409335734986976396), (-403825850161482602)⟩, true⟩

def state01 : KState := ⟨⟨362482281065258596, 362482381088490690⟩, ⟨225409626310250356, 230921563219939292⟩, true⟩

def words00 : List Nat := [371285210572505301, 371285210575330489, 371285210537581821, 371285210500556790, 371285210462475863, 371285210459231974, 371285210504213378, 371285210596579161, 371285210659921796, 371285210662847019]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 81600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 81600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501629952328876, 362501730001121367⟩, ⟨(-1353751806106270498), (-1348237783084245662)⟩, true⟩

def words01 : List Nat := [371285210745547206, 371285210864382074, 371285211030048280, 371285211083887790, 371285211112518032, 371285211142064758, 371285211264984136, 371285211320387438, 371285211524689350, 371285211730295425]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 81610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 81600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492039902474624, 362492139976752662⟩, ⟨(-571000621332251734), (-565484518049304240)⟩, true⟩

def words02 : List Nat := [371285211935055818, 371285211967235763, 371285212122967389, 371285212280192159, 371285212482838344, 371285212486302626, 371285212488465658, 371285212464681959, 371285212563011078, 371285212651128215]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 81620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 81600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485515174563167, 362485615274309436⟩, ⟨(-38323500765297452), (-32805318379522716)⟩, true⟩

def words03 : List Nat := [371285212785495708, 371285212921036573, 371285213055514985, 371285213092652239, 371285213152692582, 371285213214097259, 371285213424104453, 371285213435051294, 371285213442106768, 371285213450245798]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 81630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 81600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494730751390876, 362494830876489075⟩, ⟨(-790737117956984399), (-785216865715267081)⟩, true⟩

def words04 : List Nat := [371285213508922908, 371285213515443571, 371285213631625423, 371285213748925462, 371285213840903117, 371285213843730080, 371285213775373232, 371285213818754725, 371285214010532759, 371285214131247557]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 81640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 81600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk816A
