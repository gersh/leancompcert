import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk700A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk700B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk700A

def state06 : KState := ⟨⟨362470049409295321, 362470122258662957⟩, ⟨1062866409690902725, 1066313343877233957⟩, true⟩

def words05 : List Nat := [371285342473155591, 371285342645705216, 371285342810143668, 371285342812542428, 371285342705546145, 371285342662012206, 371285342654061759, 371285342656464124, 371285342475287600, 371285342260716586]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486909000968529, 362486981871832022⟩, ⟨(-118399579241162776), (-114951138946381766)⟩, true⟩

def words06 : List Nat := [371285342045104406, 371285342033786395, 371285341919476824, 371285341891563400, 371285341862889118, 371285341801361093, 371285341497129547, 371285341397368466, 371285341350666041, 371285341376635060]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493011718736876, 362493084611459375⟩, ⟨(-546030204070086029), (-542580232007364499)⟩, true⟩

def words07 : List Nat := [371285341402379026, 371285341428959687, 371285341637432720, 371285341764089249, 371285341953509466, 371285342143819772, 371285342288799143, 371285342291199868, 371285342310619094, 371285342424104638]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480528730109645, 362480601644181775⟩, ⟨328826455489685445, 332277923847565515⟩, true⟩

def words08 : List Nat := [371285342596601773, 371285342599001729, 371285342528942718, 371285342453879235, 371285342377875567, 371285342349925747, 371285342273949253, 371285342331523556, 371285342373952885, 371285342376438125]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494669797024682, 362494742732817525⟩, ⟨(-662452669511807883), (-658999678641714693)⟩, true⟩

def words09 : List Nat := [371285342310467089, 371285342261754345, 371285342313697762, 371285342316098065, 371285342167346614, 371285341986928043, 371285341809326849, 371285341812017833, 371285341878804742, 371285342015586078]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk700B
