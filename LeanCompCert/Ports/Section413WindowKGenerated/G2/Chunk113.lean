import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk113

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360711388460277900, 360711389163310320⟩, ⟨(-1423689218012103895), (-1423683834574707873)⟩, true⟩

def state01 : KState := ⟨⟨360548453502008092, 360548454206352335⟩, ⟨417559314906920001, 417564713174387097⟩, true⟩

def words00 : List Nat := [360585417821091073, 360585417821228801, 360585421835632493, 360585426359216848, 360585426359334791, 360585423553384489, 360585413012975479, 360585398566860841, 360585384123274039, 360585374163308515]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 11300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 11300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360378389950260657, 360378390655905166⟩, ⟨2342415206521084929, 2342420619501128759⟩, true⟩

def words01 : List Nat := [360585375398284725, 360585379896569515, 360585380293737607, 360585380293875557, 360585372965746101, 360585361912469298, 360585350861105693, 360585347568410137, 360585336553765908, 360585318272468870]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 11310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 11300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360680458275975149, 360680458982922698⟩, ⟨(-1078706989101680665), (-1078701561364888293)⟩, true⟩

def words02 : List Nat := [360585299994370579, 360585289472130280, 360585285225023507, 360585281861148889, 360585278497857391, 360585268354493723, 360585258595619428, 360585253626049018, 360585251431025696, 360585259833565635]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 11320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 11300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360490979680152971, 360490980388417976⟩, ⟨1069371003017965379, 1069376445688047549⟩, true⟩

def words03 : List Nat := [360585264263763947, 360585268693194395, 360585272916880242, 360585281042204297, 360585287145178598, 360585293247099316, 360585295460848887, 360585295460987051, 360585289978669168, 360585281662288175]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 11330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 11300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360397358248674712, 360397358958240926⟩, ⟨2131355268451483449, 2131360725883889361⟩, true⟩

def words04 : List Nat := [360585273347325131, 360585266122801995, 360585254473465702, 360585238206054835, 360585221941489333, 360585203669445526, 360585190273688974, 360585176687553675, 360585163103799227, 360585144044221886]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 11340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 11300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360639661546905780, 360639662257777548⟩, ⟨(-619883308478546673), (-619877836221522799)⟩, true⟩

def words05 : List Nat := [360585127500850026, 360585118668716843, 360585109838098482, 360585108715998353, 360585107957612779, 360585100561147731, 360585093165958642, 360585090742756607, 360585095546699353, 360585100349827410]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 11350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 11300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360625661114035136, 360625661826227692⟩, ⟨(-461467553313478523), (-461462066045744491)⟩, true⟩

def words06 : List Nat := [360585100349952897, 360585100788852224, 360585103665217920, 360585106541116886, 360585107416091047, 360585107416229632, 360585100631313434, 360585089822046085, 360585079014651486, 360585079461787824]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 11360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 11300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360466676922676937, 360466677636174822⟩, ⟨1347421385756921508, 1347426887872879958⟩, true⟩

def words07 : List Nat := [360585088147509877, 360585096831730861, 360585099726418236, 360585102927576052, 360585102927694840, 360585099737756946, 360585097651714639, 360585097651853350, 360585091107151220, 360585080701893002]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 11370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 11300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588500495480796, 360588501210290636⟩, ⟨(-39323811755716831), (-39318294703331719)⟩, true⟩

def words08 : List Nat := [360585070298432495, 360585062963904425, 360585068012666769, 360585074367037636, 360585074367167666, 360585072707428514, 360585063406206963, 360585058734811528, 360585054064197404, 360585049512046116]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 11380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 11300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360620621415486911, 360620622131618953⟩, ⟨(-405402811424214049), (-405397279305543147)⟩, true⟩

def words09 : List Nat := [360585049512169857, 360585045965364282, 360585046519662455, 360585054667987108, 360585058903214453, 360585063137724410, 360585063137848347, 360585062369503400, 360585060966609034, 360585064085894408]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 11390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 11300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 11300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk113
