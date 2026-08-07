import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk027

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360732896809707103, 360732896844115652⟩, ⟨(-524063337204665623), (-524063274051430245)⟩, true⟩

def state01 : KState := ⟨⟨361015565486380429, 361015565521057332⟩, ⟨(-1288903143674552940), (-1288903079795412436)⟩, true⟩

def words00 : List Nat := [360538997996111988, 360539135754811666, 360539173317459573, 360539210852337960, 360539210852361812, 360539323473377845, 360539571671429244, 360539819686246461, 360539955528483433, 360540130965618228]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 2700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 2700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361705000596334369, 361705000631280922⟩, ⟨(-3160264970124325138), (-3160264905513060128)⟩, true⟩

def words01 : List Nat := [360540440277599137, 360540749361566175, 360541192124640919, 360541602891981685, 360541899694381028, 360542196278305160, 360542417251471412, 360542711221329866, 360543138533636153, 360543565531864142]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 2710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 2700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361405821184173470, 361405821219393497⟩, ⟨(-2349460820481339087), (-2349460755124878669)⟩, true⟩

def words02 : List Nat := [360543922661445942, 360544148860891204, 360544366974883942, 360544584928800907, 360544763308514232, 360544899925280769, 360544960115487713, 360545020261586240, 360545212884149664, 360545528009900682]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 2720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 2700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360393410764754025, 360393410800245057⟩, ⟨422429193370841241, 422429259468561607⟩, true⟩

def words03 : List Nat := [360545975329644466, 360546422322046710, 360546800252804810, 360547048472504061, 360547257844822918, 360547467064155647, 360547592633776028, 360547638350196110, 360547638350221957, 360547582062824825]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 2730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 2700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361076110281349327, 361076110317113271⟩, ⟨(-1451950150237579672), (-1451950083390708140)⟩, true⟩

def words04 : List Nat := [360547601158031725, 360547744134477409, 360547916371331033, 360548088482699224, 360548142947365074, 360548142947394037, 360548069017248406, 360548045251345601, 360548128468577400, 360548320392216613]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 2740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 2700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361181442524631817, 361181442560672804⟩, ⟨(-1742648075120471218), (-1742648007510357100)⟩, true⟩

def words05 : List Nat := [360548408091363595, 360548495726801721, 360548713774681816, 360549022929279763, 360549254040899235, 360549484984869126, 360549648039771678, 360549819506063561, 360550048355020019, 360550277038213421]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 2750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 2700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360808725008418953, 360808725044734753⟩, ⟨(-713818778730236629), (-713818710360219195)⟩, true⟩

def words06 : List Nat := [360550516233084289, 360550628356936697, 360550672062327300, 360550715736107596, 360550715736132459, 360550681786394158, 360550827022322076, 360550972153354191, 360551028759375881, 360551121756982960]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 2760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 2700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361115529951893944, 361115529988487110⟩, ⟨(-1565833289925408330), (-1565833220785711826)⟩, true⟩

def words07 : List Nat := [360551243362465985, 360551364880251570, 360551541671692621, 360551682207228348, 360551700901239738, 360551719581790018, 360551866447456989, 360552077947847513, 360552280628461871, 360552483163321446]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 2770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 2700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361159729556688584, 361159729593561984⟩, ⟨(-1692610858189496462), (-1692610788269344728)⟩, true⟩

def words08 : List Nat := [360552614525890584, 360552720757301485, 360552802449163311, 360552884082367831, 360552928239586570, 360552978922445283, 360552978922471486, 360552963302514087, 360553059060098387, 360553276426858529]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 2780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 2700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360805061212144336, 360805061249295902⟩, ⟨(-699422106728711334), (-699422036031059208)⟩, true⟩

def words09 : List Nat := [360553620511939542, 360553964350635122, 360554205478748822, 360554439226275228, 360554591651244094, 360554743967228811, 360555022665337815, 360555178421074307, 360555267664968041, 360555356845143436]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 2790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 2700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 2700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk027
