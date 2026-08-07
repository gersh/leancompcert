import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk150

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485641429745930, 362485644366270901⟩, ⟨(-22441491089354142), (-22411694034431838)⟩, true⟩

def state01 : KState := ⟨⟨362464838092369260, 362464841032945480⟩, ⟨289707737105270421, 289737594949680895⟩, true⟩

def words00 : List Nat := [371284152287397501, 371284152287853644, 371284150016958501, 371284147773188597, 371284145529545252, 371284144639743694, 371284142572611767, 371284143292584760, 371284144003490366, 371284144003961449]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 15000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 15000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362546671901623106, 362546674846299442⟩, ⟨(-939040510181673355), (-939010590773422815)⟩, true⟩

def words01 : List Nat := [371284144187786441, 371284145657571011, 371284151554081834, 371284151554536304, 371284151552226441, 371284150336751859, 371284152330874192, 371284153333347857, 371284157496208173, 371284161658710505]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 15010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 15000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362527865505810339, 362527868454602153⟩, ⟨(-656407615177007694), (-656377633933481750)⟩, true⟩

def words02 : List Nat := [371284165851943761, 371284167406740667, 371284172858944884, 371284178310663336, 371284185006147879, 371284187787961279, 371284190559558738, 371284193330939568, 371284197287483322, 371284200193413046]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 15020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 15000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472624988758178, 362472627941649619⟩, ⟨174478506309401099, 174508549191437437⟩, true⟩

def words03 : List Nat := [371284207515593846, 371284214836988379, 371284222147760841, 371284223575326276, 371284225754347006, 371284227933305488, 371284232318886873, 371284232319342335, 371284231674704396, 371284230903696923]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 15030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 15000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476548172640601, 362476551129617458⟩, ⟨115495884150825133, 115525988497760531⟩, true⟩

def words04 : List Nat := [371284231935526940, 371284232016499557, 371284233814468056, 371284235612372314, 371284236007600660, 371284236008056353, 371284230530490513, 371284228290852762, 371284227274552358, 371284227275032592]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 15040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 15000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362454645771468220, 362454648732588708⟩, ⟨445520362466772321, 445550529196802657⟩, true⟩

def words05 : List Nat := [371284226765365064, 371284225906456569, 371284228590596409, 371284230501182025, 371284233757003750, 371284237012572347, 371284239300259929, 371284239300715954, 371284235725137150, 371284233761087832]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 15050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 15000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362431909475815098, 362431912441000445⟩, ⟨788206640602290325, 788236868570114133⟩, true⟩

def words06 : List Nat := [371284234230011445, 371284234230468827, 371284232213129608, 371284230192255059, 371284228171463274, 371284226548239767, 371284222981543535, 371284221146957414, 371284219312465804, 371284217475411203]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 15060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 15000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507694400516861, 362507697369836613⟩, ⟨(-354323992739196648), (-354293702445048770)⟩, true⟩

def words07 : List Nat := [371284214005151888, 371284212353613204, 371284213440688167, 371284213441144749, 371284210328787452, 371284206328201052, 371284202716102163, 371284202716613493, 371284203091967041, 371284204650358790]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 15070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 15000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362446363553869632, 362446366527307283⟩, ⟨570596808648489810, 570627161061786118⟩, true⟩

def words08 : List Nat := [371284205400494277, 371284205400951140, 371284200305882824, 371284199596178050, 371284198886348560, 371284198338748115, 371284193337272547, 371284188096408071, 371284182856046952, 371284181448517475]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 15080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 15000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362397379572965374, 362397382550521165⟩, ⟨1310391970090477019, 1310422384667474703⟩, true⟩

def words09 : List Nat := [371284180818363246, 371284182693945894, 371284184518037046, 371284184518494282, 371284180505577485, 371284177832240665, 371284176114139349, 371284176114596662, 371284171236988959, 371284165489903117]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 15090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 15000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 15000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk150
