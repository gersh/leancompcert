import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk839A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk839B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk839A

def state06 : KState := ⟨⟨360594357442417144, 360594403530074235⟩, ⟨(-1004997291603757154), (-1002384059623121510)⟩, true⟩

def words05 : List Nat := [360582465228445739, 360582465132978732, 360582465037138925, 360582465023779698, 360582464969363534, 360582464792105740, 360582464614621393, 360582464556930717, 360582464700103245, 360582464843545691]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566145514590072, 360566191613729147⟩, ⟨1363672524759101837, 1366286720824094087⟩, true⟩

def words06 : List Nat := [360582464901497710, 360582464902702819, 360582464818926318, 360582464690472159, 360582464561719155, 360582464336621327, 360582463969784622, 360582463513609305, 360582463057213416, 360582462742951776]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360553469045688806, 360553515156199445⟩, ⟨2428249346679443549, 2430864497669628683⟩, true⟩

def words07 : List Nat := [360582462550155313, 360582462470349842, 360582462390395345, 360582462219831093, 360582462036375549, 360582461816280693, 360582461595837325, 360582461482740395, 360582461254532013, 360582460911113349]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595879011902661, 360595925133782143⟩, ⟨(-1133561108299631933), (-1130945002496879117)⟩, true⟩

def words08 : List Nat := [360582460567417507, 360582460336276073, 360582460175854182, 360582460157325394, 360582460138709857, 360582459981066686, 360582459829977265, 360582459820903018, 360582459898547356, 360582460060113573]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569600286811945, 360569646420192563⟩, ⟨1073722336144458338, 1076339407983760618⟩, true⟩

def words09 : List Nat := [360582460150537305, 360582460241090405, 360582460259433966, 360582460349140665, 360582460384845500, 360582460420756144, 360582460421844607, 360582460349646910, 360582460135716653, 360582459984573323]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk839B
