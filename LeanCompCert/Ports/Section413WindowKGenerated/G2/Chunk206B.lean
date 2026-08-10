import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk206A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk206B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk206A

def state06 : KState := ⟨⟨360604909136841538, 360604911621471935⟩, ⟨(-478767385478520409), (-478732648761818775)⟩, true⟩

def words05 : List Nat := [360581739844986775, 360581740866425809, 360581742887796794, 360581743906902119, 360581743907149550, 360581742668188248, 360581741429300958, 360581739096902278, 360581739663367820, 360581740785173508]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 20650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 20600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360535848630769683, 360535851117924980⟩, ⟨948049582602091810, 948084371495713172⟩, true⟩

def words06 : List Nat := [360581740785409809, 360581740344191490, 360581737564939986, 360581737116065355, 360581736667156511, 360581735630587355, 360581732256516044, 360581727645271696, 360581723034424311, 360581718770150221]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 20660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 20600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360416400028398451, 360416402518055840⟩, ⟨3417664934936080415, 3417699775560439663⟩, true⟩

def words07 : List Nat := [360581716551431313, 360581714275850183, 360581712000461057, 360581708541458649, 360581702746788171, 360581696312337628, 360581689878432696, 360581683078883626, 360581676456343067, 360581668464649672]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 20670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 20600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360449273242858593, 360449275735020134⟩, ⟨2737783398310472031, 2737818290733283001⟩, true⟩

def words08 : List Nat := [360581660473667423, 360581654809507954, 360581650358703498, 360581645413315525, 360581640468389020, 360581633384023445, 360581623966589745, 360581616196956778, 360581608427998021, 360581601413644266]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 20680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 20600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360415084769511413, 360415087264208584⟩, ⟨3445422039991589127, 3445456984888899611⟩, true⟩

def words09 : List Nat := [360581595018559703, 360581586731158772, 360581578444503614, 360581572481866459, 360581567713436461, 360581562360244159, 360581557007538860, 360581550489816912, 360581542502555925, 360581534461546213]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 20690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 20600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 20600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk206B
