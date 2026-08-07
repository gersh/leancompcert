import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk725

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

def state06 : KState := ⟨⟨360592258775176389, 360592292805328719⟩, ⟨(-720536999118561087), (-718869174148079921)⟩, true⟩

def words05 : List Nat := [360582385995174494, 360582386066463001, 360582386193923818, 360582386194954061, 360582386132894780, 360582385893583127, 360582385654071668, 360582385482167407, 360582385566470733, 360582385704073940]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589054039827429, 360589088079804222⟩, ⟨(-488029748702144391), (-486361210820916415)⟩, true⟩

def words06 : List Nat := [360582385713384511, 360582385777955249, 360582385992741282, 360582386207823717, 360582386322852590, 360582386381939983, 360582386382873060, 360582386298146374, 360582386213239214, 360582386212518104]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360576536367476803, 360576570417162918⟩, ⟨420456106134148981, 422125348670783549⟩, true⟩

def words07 : List Nat := [360582386420049260, 360582386627771406, 360582386699489457, 360582386700520074, 360582386627344157, 360582386506957309, 360582386454210200, 360582386496250596, 360582386497173299, 360582386418109058]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591882800011186, 360591916859434909⟩, ⟨(-693473794399402005), (-691803845059227899)⟩, true⟩

def words08 : List Nat := [360582386416792748, 360582386591605423, 360582386762267831, 360582386933108781, 360582386943821826, 360582386944852521, 360582386765984869, 360582386690351656, 360582386614422096, 360582386699428032]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583202968074931, 360583237037313136⟩, ⟨(-63319868571152727), (-61649206749803143)⟩, true⟩

def words09 : List Nat := [360582386737207826, 360582386775103828, 360582386966900401, 360582387281469053, 360582387547611622, 360582387813914967, 360582387932093077, 360582387933123976, 360582387873500524, 360582387886382023]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk725
