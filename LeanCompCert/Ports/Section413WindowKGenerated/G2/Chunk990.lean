import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk990

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

def state06 : KState := ⟨⟨360582700269784423, 360582765253420911⟩, ⟨(-37485193584680865), (-33138565106795747)⟩, true⟩

def words05 : List Nat := [360582429912688221, 360582429979308801, 360582430147519984, 360582430367524020, 360582430521375878, 360582430675452067, 360582430746962163, 360582430748401868, 360582430721535223, 360582430726562644]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360579516908999641, 360579581906187143⟩, ⟨277817801634778580, 282165772543539318⟩, true⟩

def words06 : List Nat := [360582430736635197, 360582430738074974, 360582430646667608, 360582430503592869, 360582430360259358, 360582430191511326, 360582430107225264, 360582430105757750, 360582430104133037, 360582430051665528]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583219547958626, 360583284558758483⟩, ⟨(-89094790905146074), (-84745471352483502)⟩, true⟩

def words07 : List Nat := [360582430024101211, 360582429994504347, 360582429964475207, 360582429965141981, 360582429864114971, 360582429676532013, 360582429488679226, 360582429316954616, 360582429233576243, 360582429243699567]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586425768394183, 360586490792915543⟩, ⟨(-406886718100819272), (-402536038955902206)⟩, true⟩

def words08 : List Nat := [360582429244994492, 360582429196479716, 360582429067213880, 360582429040175726, 360582429012777717, 360582428902368124, 360582428805820280, 360582428658422038, 360582428510740868, 360582428506341022]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360560284652126273, 360560349690228459⟩, ⟨2183629110419243869, 2187981135355298911⟩, true⟩

def words09 : List Nat := [360582428635580529, 360582428765118731, 360582428807156260, 360582428808596519, 360582428749004647, 360582428664029735, 360582428578633996, 360582428554913250, 360582428429543839, 360582428208244154]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk990
