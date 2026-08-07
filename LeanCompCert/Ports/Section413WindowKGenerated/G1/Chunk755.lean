import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk755

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485300645052774, 362485385740449931⟩, ⟨(-17642220382231715), (-13303573596359017)⟩, true⟩

def state01 : KState := ⟨⟨362476820291830648, 362476905410738953⟩, ⟨622679290053085102, 627019712046372758⟩, true⟩

def words00 : List Nat := [371285209540122863, 371285209542767082, 371285209431307687, 371285209465497764, 371285209551757354, 371285209554361985, 371285209459057755, 371285209364656855, 371285209269257675, 371285209207746587]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 75500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 75500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362467125679924826, 362467210822264212⟩, ⟨1354840712005262799, 1359182903396086415⟩, true⟩

def words01 : List Nat := [371285209164776188, 371285209232852888, 371285209300077370, 371285209302683645, 371285209190332761, 371285209085046396, 371285208978394323, 371285208950580054, 371285208712594868, 371285208477235029]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 75510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 75500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487773046053098, 362487858211693858⟩, ⟨(-204548371103635674), (-200204419875010578)⟩, true⟩

def words02 : List Nat := [371285208240685049, 371285208180412228, 371285208041319112, 371285207976496045, 371285207910895800, 371285207830011043, 371285207590994091, 371285207528525353, 371285207548014310, 371285207585859764]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 75520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 75500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489269549228299, 362489354738498233⟩, ⟨(-317570991755080662), (-313225255691454604)⟩, true⟩

def words03 : List Nat := [371285207600033093, 371285207615059375, 371285207804165840, 371285207906788375, 371285208061710988, 371285208217659656, 371285208314186981, 371285208316787475, 371285208253234582, 371285208311317081]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 75530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 75500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484194845802369, 362484280058245793⟩, ⟨65825191847405624, 70172678554401084⟩, true⟩

def words04 : List Nat := [371285208543062807, 371285208561423049, 371285208570213973, 371285208579952963, 371285208621343307, 371285208624238663, 371285208676806513, 371285208778780072, 371285208879885859, 371285208882581391]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 75540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 75500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498358404914220, 362498443640920652⟩, ⟨(-1004317954364739913), (-999968687353717005)⟩, true⟩

def words05 : List Nat := [371285208908254805, 371285208947576171, 371285209160554736, 371285209172013121, 371285209174048000, 371285209149747027, 371285209272320153, 371285209359840255, 371285209536765643, 371285209714856231]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473536411823501, 362473621671284902⟩, ⟨871303968334413266, 875655007724895154⟩, true⟩

def words06 : List Nat := [371285209889475224, 371285209892076299, 371285209846819810, 371285209863617620, 371285209865481270, 371285209857625332, 371285209615756682, 371285209374810491, 371285209132786368, 371285209007631666]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475023186211032, 362475108469073369⟩, ⟨758998967509167855, 763351775428589875⟩, true⟩

def words07 : List Nat := [371285208877700993, 371285208902184163, 371285208925426036, 371285208928030034, 371285208762000330, 371285208650837689, 371285208598951202, 371285208601559455, 371285208517451179, 371285208386715981]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494471867300902, 362494557173459510⟩, ⟨(-711005784151320872), (-706651215380497468)⟩, true⟩

def words08 : List Nat := [371285208254862482, 371285208214685950, 371285208224564973, 371285208318936086, 371285208384771373, 371285208387418881, 371285208381661917, 371285208458991107, 371285208695896184, 371285208822261875]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485182703036175, 362485268033001970⟩, ⟨(-8775013247381922), (-4418644781550886)⟩, true⟩

def words09 : List Nat := [371285208923446104, 371285209025529665, 371285209199637837, 371285209298446175, 371285209429748375, 371285209562011690, 371285209686967445, 371285209689570050, 371285209581964396, 371285209586092782]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk755
