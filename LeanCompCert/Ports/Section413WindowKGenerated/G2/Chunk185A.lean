import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk185A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360629373483145489, 360629375455799881⟩, ⟨(-820157182551176790), (-820132481208709616)⟩, true⟩

def state01 : KState := ⟨⟨360667202796639471, 360667204771540842⟩, ⟨(-1520519744163057167), (-1520495001240246027)⟩, true⟩

def words00 : List Nat := [360585046508075803, 360585047088292549, 360585050584243444, 360585054079887469, 360585056826422539, 360585058373319269, 360585058373529510, 360585058341751473, 360585060254727802, 360585064692601820]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 18500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 18500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360552278979738363, 360552280956859689⟩, ⟨607400858059709610, 607425642085080974⟩, true⟩

def words01 : List Nat := [360585071231382052, 360585077769501982, 360585081686382036, 360585082705884592, 360585082706085729, 360585081297598781, 360585081391849348, 360585081392085378, 360585081088484775, 360585079317663420]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 18510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 18500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360692353866796152, 360692355846148734⟩, ⟨(-1987232886864938644), (-1987208061506109170)⟩, true⟩

def words02 : List Nat := [360585078686215048, 360585082066304963, 360585088355558386, 360585094644179362, 360585098543853006, 360585100788591509, 360585104928699621, 360585109068429552, 360585113101084382, 360585118888536835]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 18520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 18500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360712690906903749, 360712692888505597⟩, ⟨(-2364425507793206477), (-2364400640744486589)⟩, true⟩

def words03 : List Nat := [360585122726564389, 360585126564201600, 360585132134224530, 360585139165320696, 360585144205215339, 360585149244607388, 360585152333712507, 360585156308899493, 360585163188086298, 360585170066611175]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 18530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 18500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360746490040594243, 360746492024423525⟩, ⟨(-2991358070939484473), (-2991333162583074735)⟩, true⟩

def words04 : List Nat := [360585179848476499, 360585187810017517, 360585193531855279, 360585199253098831, 360585204227110470, 360585211404690629, 360585219521802342, 360585227638083472, 360585234171744249, 360585242864670247]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 18540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 18500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk185A
