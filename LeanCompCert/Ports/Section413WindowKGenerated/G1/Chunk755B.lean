import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk755A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk755B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk755A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk755B
