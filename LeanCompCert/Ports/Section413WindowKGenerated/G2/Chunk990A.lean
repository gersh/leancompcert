import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk990A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584416843223692, 360584481745146357⟩, ⟨(-207792645760546084), (-203454109403300192)⟩, true⟩

def state01 : KState := ⟨⟨360579850404473543, 360579915319955436⟩, ⟨244262169463853530, 248602048253526416⟩, true⟩

def words00 : List Nat := [360582426693334356, 360582426694773355, 360582426646770948, 360582426536844381, 360582426426684863, 360582426291072754, 360582426232239691, 360582426245961220, 360582426247258937, 360582426198131919]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360597905770635249, 360597970699686259⟩, ⟨(-1543537792389749687), (-1539196570053947571)⟩, true⟩

def words01 : List Nat := [360582426173943202, 360582426165882165, 360582426249695199, 360582426282102176, 360582426283454838, 360582426209198413, 360582426160914605, 360582426240211166, 360582426398357456, 360582426556827129]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593668450301752, 360593733393075787⟩, ⟨(-1123939993331366508), (-1119597412073199994)⟩, true⟩

def words02 : List Nat := [360582426650417043, 360582426797906711, 360582427047010966, 360582427296532981, 360582427482669695, 360582427597563461, 360582427661265155, 360582427725113848, 360582427752616642, 360582427868421152]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584786892677524, 360584851849004183⟩, ⟨(-244322170023484456), (-239978246581361450)⟩, true⟩

def words03 : List Nat := [360582428065509546, 360582428262869941, 360582428383136011, 360582428477536925, 360582428526881305, 360582428576649786, 360582428701089121, 360582428778081163, 360582428803828855, 360582428829784049]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594519320409798, 360594584290344062⟩, ⟨(-1208255115791003959), (-1203909844585180063)⟩, true⟩

def words04 : List Nat := [360582428957303033, 360582429157309207, 360582429354426755, 360582429551805781, 360582429662853649, 360582429672363159, 360582429673534728, 360582429670668623, 360582429721995252, 360582429846223507]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk990A
