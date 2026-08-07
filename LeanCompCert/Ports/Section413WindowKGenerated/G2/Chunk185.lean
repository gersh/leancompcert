import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk185

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

def state06 : KState := ⟨⟨360749099895191912, 360749101881249997⟩, ⟨(-3039837757760303096), (-3039812808048022668)⟩, true⟩

def words05 : List Nat := [360585252338558776, 360585261811493972, 360585274183417789, 360585283669775413, 360585290685711151, 360585297700909398, 360585303136496384, 360585310038147222, 360585318863330171, 360585327687615602]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 18550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 18500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360653383168305131, 360653385156615831⟩, ⟨(-1263354057414361201), (-1263329065882419499)⟩, true⟩

def words06 : List Nat := [360585334622727283, 360585338674699644, 360585343935239642, 360585349195287651, 360585353124033247, 360585354170593229, 360585354170805901, 360585353742336034, 360585354511980190, 360585358175522599]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 18560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 18500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360548087289994822, 360548089280536816⟩, ⟨692539353552241669, 692564386530616479⟩, true⟩

def words07 : List Nat := [360585361667068541, 360585365158280363, 360585366759923644, 360585366896474257, 360585366896672676, 360585366261873468, 360585365775454499, 360585366011148580, 360585366011360850, 360585364005323179]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 18570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 18500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360673312914391390, 360673314907168328⟩, ⟨(-1634881678448694889), (-1634856603934190413)⟩, true⟩

def words08 : List Nat := [360585361999448665, 360585361756853637, 360585365468803188, 360585369180398817, 360585370036424212, 360585370036661072, 360585368886649940, 360585369756811476, 360585372109506143, 360585376840150191]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 18580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 18500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360668121502920932, 360668123497953840⟩, ⟨(-1538211982837122006), (-1538186866372725690)⟩, true⟩

def words09 : List Nat := [360585380109993404, 360585383379514806, 360585389536522478, 360585397145770943, 360585404009527918, 360585410872585331, 360585416276459369, 360585420832486550, 360585425279061423, 360585429725233410]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 18590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 18500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 18500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk185
