import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk120

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602317443334463, 360602318240687312⟩, ⟨(-249913415443900068), (-249906932810502878)⟩, true⟩

def state01 : KState := ⟨⟨360616559045324823, 360616559844062772⟩, ⟨(-421161135758726470), (-421154636497090262)⟩, true⟩

def words00 : List Nat := [360581497119036322, 360581497877092974, 360581497877224154, 360581495151353966, 360581492425916160, 360581484974200801, 360581487206988165, 360581491766093435, 360581492846700145, 360581495766425849]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 12000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 12000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360643969796276448, 360643970596406330⟩, ⟨(-750222267925126265), (-750215751939569733)⟩, true⟩

def words01 : List Nat := [360581505567714245, 360581515367418037, 360581529018226502, 360581535800190055, 360581536584943303, 360581537369576128, 360581542644584228, 360581551447123301, 360581556640185821, 360581561832415018]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 12010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 12000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360532585066576445, 360532585868109288⟩, ⟨588391865361325387, 588398398217536111⟩, true⟩

def words02 : List Nat := [360581563556544114, 360581563556691453, 360581558422480511, 360581554285281581, 360581550148731442, 360581541211517353, 360581532590374742, 360581519650501207, 360581506712751220, 360581496790654387]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 12020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 12000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360485090457232294, 360485091260156402⟩, ⟨1160118545911753635, 1160125095511830757⟩, true⟩

def words03 : List Nat := [360581492823279428, 360581492921324121, 360581492921458994, 360581487595861851, 360581481512473518, 360581471963253942, 360581462415577820, 360581459719343686, 360581455168590933, 360581447165099246]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 12030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 12000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360688409125609406, 360688409929926037⟩, ⟨(-1288634528156088022), (-1288627961783024326)⟩, true⟩

def words04 : List Nat := [360581439162901310, 360581440719422413, 360581450275308784, 360581459829636495, 360581462739043904, 360581462952345691, 360581462972500517, 360581462992692820, 360581469849957081, 360581478724069011]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 12040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 12000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360633391029523722, 360633391835248903⟩, ⟨(-625348050633075934), (-625341467280195684)⟩, true⟩

def words05 : List Nat := [360581482998942814, 360581487273121713, 360581493721356742, 360581506099704172, 360581516750157688, 360581527398869429, 360581534610647814, 360581535008748214, 360581539308770750, 360581543608130075]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 12050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 12000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571334373485149, 360571335180605227⟩, ⟨123000269545741117, 123006869728122587⟩, true⟩

def words06 : List Nat := [360581547724550201, 360581548657943584, 360581548658075428, 360581546164570255, 360581543671453993, 360581537554003530, 360581534932238567, 360581533322536141, 360581531713083303, 360581526304857765]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 12060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 12000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360714078250374522, 360714079058891220⟩, ⟨(-1600675809377259808), (-1600669192330873822)⟩, true⟩

def words07 : List Nat := [360581531423974589, 360581537386411543, 360581550154086612, 360581556125086400, 360581556125225480, 360581555327599422, 360581555615743180, 360581562360850854, 360581573330896155, 360581584299158510]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 12070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 12000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583618097219496, 360583618907148335⟩, ⟨(-24070163433939750), (-24063529322067608)⟩, true⟩

def words08 : List Nat := [360581591852472607, 360581599687988118, 360581611605434547, 360581623520951956, 360581633720125473, 360581637136245287, 360581637136378895, 360581635597279151, 360581634058408776, 360581628705401411]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 12080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 12000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360453510061220970, 360453510872546269⟩, ⟨1549782596447494509, 1549789247449603435⟩, true⟩

def words09 : List Nat := [360581633709885458, 360581638713569991, 360581639397561070, 360581639397709348, 360581633308167193, 360581623075870827, 360581612845218863, 360581609393171992, 360581603214523189, 360581592628533840]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 12090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 12000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 12000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk120
