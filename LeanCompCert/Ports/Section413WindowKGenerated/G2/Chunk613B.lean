import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk613A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk613B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk613A

def state06 : KState := ⟨⟨360587876644463570, 360587900657154908⟩, ⟨(-330808340085202988), (-329812969878353894)⟩, true⟩

def words05 : List Nat := [360582523773396341, 360582524404370730, 360582524849094956, 360582525029313040, 360582525030044997, 360582525030218037, 360582525294775741, 360582525519493650, 360582525607859580, 360582525696351167]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 61350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 61300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360617779208485378, 360617803229304402⟩, ⟨(-2165708450105883240), (-2164712581144738900)⟩, true⟩

def words06 : List Nat := [360582525949780536, 360582526405305105, 360582527125903077, 360582527846644385, 360582528342791402, 360582528656439878, 360582529180208219, 360582529704211856, 360582530088746448, 360582530664393537]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 61360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 61300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360609217961972270, 360609241990986875⟩, ⟨(-1640272485400717770), (-1639276113437613808)⟩, true⟩

def words07 : List Nat := [360582531105608174, 360582531546894739, 360582532066035970, 360582532739332196, 360582533340106524, 360582533941015825, 360582534376046680, 360582534546790405, 360582534982602088, 360582535418701680]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 61370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 61300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605521997901531, 360605546035024455⟩, ⟨(-1413413595531496719), (-1412416725839207985)⟩, true⟩

def words08 : List Nat := [360582536119714725, 360582536642847621, 360582536937023944, 360582537231270964, 360582537457724281, 360582537854092892, 360582538210104588, 360582538566266802, 360582538757268159, 360582539132940450]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 61380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 61300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360595885977994633, 360595910023232507⟩, ⟨(-821846968981814368), (-820849601071992618)⟩, true⟩

def words09 : List Nat := [360582539548895745, 360582539965085328, 360582540478032363, 360582540726872997, 360582540751445374, 360582540776084157, 360582540777254754, 360582540917893144, 360582541136329868, 360582541354952317]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 61390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 61300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 61300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk613B
