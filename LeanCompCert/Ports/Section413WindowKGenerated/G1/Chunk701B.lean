import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk701A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk701B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk701A

def state06 : KState := ⟨⟨362489639823835855, 362489712889433619⟩, ⟨(-310430972491916583), (-306968878393434851)⟩, true⟩

def words05 : List Nat := [371285338474263314, 371285338322029756, 371285338170997775, 371285338173441957, 371285338008495115, 371285337811919878, 371285337618014371, 371285337620679461, 371285337617625991, 371285337682717731]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471312126226182, 362471385213514012⟩, ⟨975501403799111793, 978965019785320937⟩, true⟩

def words06 : List Nat := [371285337715140348, 371285337717542940, 371285337479256610, 371285337444947972, 371285337434125032, 371285337436527697, 371285337192528695, 371285336942228630, 371285336690900946, 371285336546274242]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463535960867357, 362463609069769342⟩, ⟨1521258438038633314, 1524723570796642496⟩, true⟩

def words07 : List Nat := [371285336349085492, 371285336324057269, 371285336298260661, 371285336263005228, 371285336033219180, 371285335810753114, 371285335587003663, 371285335566669273, 371285335275350574, 371285334968469779]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473619638621859, 362473692769037459⟩, ⟨813630516307065178, 817097159002989840⟩, true⟩

def words08 : List Nat := [371285334660530186, 371285334556307462, 371285334397044355, 371285334420537568, 371285334422397102, 371285334413295644, 371285334193176222, 371285334108100461, 371285334021836947, 371285333988000317]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470948460735810, 362471021613103816⟩, ⟨1001132536614276117, 1004600720253470557⟩, true⟩

def words09 : List Nat := [371285333823975475, 371285333622375725, 371285333419775326, 371285333347566225, 371285333172816706, 371285333038834383, 371285332904016909, 371285332770251586, 371285332365483217, 371285332164674379]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk701B
