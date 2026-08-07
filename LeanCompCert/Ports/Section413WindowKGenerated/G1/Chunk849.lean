import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk849

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489844147095883, 362489952727835082⟩, ⟨(-399677967447057997), (-393453474562554983)⟩, true⟩

def state01 : KState := ⟨⟨362484918340030214, 362485026947055229⟩, ⟨18547008628392111, 24773733316718983⟩, true⟩

def words00 : List Nat := [371285318634533255, 371285318637482490, 371285318621513465, 371285318585372204, 371285318551159171, 371285318554441071, 371285318573024962, 371285318650073156, 371285318708561820, 371285318711668546]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 84900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 84900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493860547142287, 362493969180857269⟩, ⟨(-740790360704485253), (-734561369641068195)⟩, true⟩

def words01 : List Nat := [371285318776973131, 371285318847280581, 371285319054581696, 371285319078006665, 371285319080320497, 371285319058166104, 371285319067390100, 371285319070640931, 371285319137813063, 371285319243036930]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 84910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 84900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479525347211325, 362479634007532345⟩, ⟨476600403678582331, 482831654261692203⟩, true⟩

def words02 : List Nat := [371285319347052827, 371285319350002775, 371285319309119528, 371285319352805312, 371285319426972505, 371285319429922502, 371285319319451603, 371285319209991228, 371285319099300506, 371285319061744776]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 84920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 84900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468771109088331, 362468879795950541⟩, ⟨1390011420420012708, 1396244925285290460⟩, true⟩

def words03 : List Nat := [371285318996857211, 371285318950209488, 371285318902605188, 371285318855922423, 371285318623627851, 371285318435280831, 371285318245381749, 371285318180787783, 371285318000377679, 371285317810140385]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 84930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 84900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474472069327042, 362474580782602814⟩, ⟨905794065926587683, 912029814493479671⟩, true⟩

def words04 : List Nat := [371285317618620619, 371285317516069928, 371285317377070320, 371285317367496179, 371285317357004472, 371285317311441454, 371285317080253774, 371285316989017235, 371285316896294419, 371285316860466187]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 84940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 84900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362465947111015700, 362466055851262960⟩, ⟨1630065246130671541, 1636303286054613169⟩, true⟩

def words05 : List Nat := [371285316736313084, 371285316613451795, 371285316489319989, 371285316437837140, 371285316316015664, 371285316220958013, 371285316124932015, 371285316029604325, 371285315764498746, 371285315541541381]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470222590467541, 362470331357010186⟩, ⟨1266811748749738853, 1273052022863439503⟩, true⟩

def words06 : List Nat := [371285315316854252, 371285315231538075, 371285314995939590, 371285314750281081, 371285314503502729, 371285314300415403, 371285314052685319, 371285313944609750, 371285313835512735, 371285313727527586]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482396574800556, 362482505368016237⟩, ⟨232304754631021728, 238547295288802530⟩, true⟩

def words07 : List Nat := [371285313553207516, 371285313497188013, 371285313439705803, 371285313432939709, 371285313240962206, 371285313003702092, 371285312765205777, 371285312666360232, 371285312496965062, 371285312467278285]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468516620444284, 362468625440263657⟩, ⟨1411851466742870429, 1418096268322048805⟩, true⟩

def words08 : List Nat := [371285312436463191, 371285312404586886, 371285312187233274, 371285312058938791, 371285311929163522, 371285311816672060, 371285311579185421, 371285311313452656, 371285311046552048, 371285310888767270]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362464632533080813, 362464741379522029⟩, ⟨1742054475162300987, 1748301539463628379⟩, true⟩

def words09 : List Nat := [371285310694449190, 371285310639702129, 371285310583916994, 371285310518535348, 371285310371609471, 371285310257901817, 371285310142675108, 371285310099717381, 371285309871551932, 371285309632927484]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk849
