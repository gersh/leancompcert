import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk725A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360611948318133535, 360611982289801929⟩, ⟨(-2147652310358417335), (-2145988727223051083)⟩, true⟩

def state01 : KState := ⟨⟨360605749768814154, 360605783750286310⟩, ⟨(-1698364615194433733), (-1696700321237243529)⟩, true⟩

def words00 : List Nat := [360582383105708262, 360582383168046736, 360582383420077826, 360582383672417367, 360582383810161456, 360582383953519686, 360582384002067058, 360582384050725217, 360582384213582543, 360582384537460157]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589071311473951, 360589105302655307⟩, ⟨(-488872213049787671), (-487207215029817157)⟩, true⟩

def words01 : List Nat := [360582384988712404, 360582385440156184, 360582385745846303, 360582385995536216, 360582386196838735, 360582386398408564, 360582386747981691, 360582386961801541, 360582387055361650, 360582387149085585]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576856248527077, 360576890249427982⟩, ⟨397091634192715166, 398757337122058646⟩, true⟩

def words02 : List Nat := [360582387371486421, 360582387731836661, 360582388040300343, 360582388348945234, 360582388493681407, 360582388494711220, 360582388449573826, 360582388324203006, 360582388198534793, 360582388075667084]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574287781696851, 360574321792416950⟩, ⟨583448499984218428, 585114915146419130⟩, true⟩

def words03 : List Nat := [360582388000793791, 360582387830049643, 360582387677080769, 360582387881540763, 360582388006256370, 360582388131136372, 360582388161302644, 360582388162332682, 360582388002712859, 360582387892708464]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573682062088052, 360573716082517440⟩, ⟨627338563396109008, 629005682918855498⟩, true⟩

def words04 : List Nat := [360582387782362530, 360582387618323699, 360582387471437964, 360582387230098380, 360582386988603411, 360582386624330525, 360582386360734607, 360582386287030348, 360582386213207435, 360582386043687928]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk725A
