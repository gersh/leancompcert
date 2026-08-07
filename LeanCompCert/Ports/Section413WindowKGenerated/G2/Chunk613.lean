import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk613

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567703816864140, 360567727780768140⟩, ⟨905301932622032732, 906294310703365850⟩, true⟩

def state01 : KState := ⟨⟨360609355559783962, 360609379531795683⟩, ⟨(-1648163239096230225), (-1647170363972472259)⟩, true⟩

def words00 : List Nat := [360582512113051076, 360582512180863630, 360582512350946513, 360582512521184005, 360582512521976282, 360582512465759500, 360582512682642729, 360582512899784362, 360582513271503747, 360582513710589497]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360601673035419579, 360601697015624224⟩, ⟨(-1177153242784413925), (-1176159865312727979)⟩, true⟩

def words01 : List Nat := [360582514001925550, 360582514293346053, 360582514495899624, 360582514903761680, 360582515243534623, 360582515583436828, 360582515787669946, 360582516011870663, 360582516325368932, 360582516639157554]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360568662338828529, 360568686327117892⟩, ⟨847163869878241326, 848157743146934728⟩, true⟩

def words02 : List Nat := [360582516940401732, 360582516976949112, 360582516977714570, 360582516880782295, 360582516783718563, 360582516497270979, 360582516345997338, 360582516187678530, 360582516029270911, 360582515737571943]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360631062898877495, 360631086895279427⟩, ⟨(-2980184390987643955), (-2979190020135117557)⟩, true⟩

def words03 : List Nat := [360582515552931027, 360582515594031135, 360582515900500197, 360582516325863865, 360582516517379704, 360582516708956608, 360582517103548427, 360582517630744120, 360582518423243029, 360582519215911059]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614095942832309, 360614119947432205⟩, ⟨(-1939490449179251641), (-1938495575423823581)⟩, true⟩

def words04 : List Nat := [360582519783269646, 360582520086009874, 360582520654116742, 360582521222467232, 360582521722862593, 360582522073840892, 360582522205395432, 360582522337046050, 360582522626557814, 360582523142564741]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk613
