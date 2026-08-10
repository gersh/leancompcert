import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk701A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk701B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk701A

def state06 : KState := ⟨⟨360585361476966643, 360585393208245603⟩, ⟨(-202109085927727909), (-200605325035818469)⟩, true⟩

def words05 : List Nat := [360582535920139727, 360582535616686126, 360582535312949754, 360582535096912999, 360582534886446538, 360582534503226158, 360582534119826522, 360582533939395432, 360582533952299105, 360582533994080529]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 70150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 70100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561589281434086, 360561621022189240⟩, ⟨1465767030780943301, 1467271456570250727⟩, true⟩

def words06 : List Nat := [360582533994985854, 360582533870148343, 360582533542310421, 360582533417404505, 360582533292228659, 360582533116240368, 360582532737348592, 360582532234502623, 360582531731468591, 360582531260988874]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 70160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 70100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360539681965698232, 360539713715813461⟩, ⟨3003177788270095073, 3004682870901863109⟩, true⟩

def words07 : List Nat := [360582530963803134, 360582530805147986, 360582530646399320, 360582530360606511, 360582530015475125, 360582529529370294, 360582529042984371, 360582528759336755, 360582528272848130, 360582527663817193]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 70100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360564482974817300, 360564514734324062⟩, ⟨1262635297473595889, 1264141039250553487⟩, true⟩

def words08 : List Nat := [360582527054570602, 360582526648183581, 360582526402854634, 360582526360239117, 360582526317546945, 360582526101974387, 360582525799145375, 360582525556364850, 360582525313314116, 360582525007001802]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 70180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 70100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360552462394242466, 360552494163228577⟩, ⟨2106392902679386348, 2107899309857089588⟩, true⟩

def words09 : List Nat := [360582524751312622, 360582524341305458, 360582523931121415, 360582523590664229, 360582523352232067, 360582523026921763, 360582522701493687, 360582522274896749, 360582521645513975, 360582521218924547]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 70190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 70100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 70100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk701B
