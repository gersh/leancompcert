import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk712A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk712B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk712A

def state06 : KState := ⟨⟨360555682724068882, 360555715498665789⟩, ⟨1893991821436330589, 1895569356863105907⟩, true⟩

def words05 : List Nat := [360582319524250304, 360582319314563244, 360582319104802083, 360582318725436554, 360582318255560027, 360582317736239628, 360582317216637440, 360582316893778952, 360582316619661405, 360582316247428954]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574938314593349, 360574971098726764⟩, ⟨521861522167528121, 523439737213623275⟩, true⟩

def words06 : List Nat := [360582315874959893, 360582315699316472, 360582315805302830, 360582315957148260, 360582315958080493, 360582315942117282, 360582315867826052, 360582315789712733, 360582315711313139, 360582315559751230]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571476728052766, 360571509521820993⟩, ⟨768622735895417979, 770201637661235235⟩, true⟩

def words07 : List Nat := [360582315457610525, 360582315256661899, 360582315055525306, 360582315122937610, 360582315182867199, 360582315242958905, 360582315243860882, 360582315179300593, 360582314970186917, 360582314819767981]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360561965295015024, 360561998098305221⟩, ⟨1446560927190576374, 1448140507731064156⟩, true⟩

def words08 : List Nat := [360582314669014487, 360582314430293021, 360582314087474083, 360582313646529196, 360582313205432099, 360582312682646472, 360582312259643988, 360582312033239104, 360582311806719110, 360582311473361065]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576364732957826, 360576397545792963⟩, ⟨419927235424752850, 421507496469494620⟩, true⟩

def words09 : List Nat := [360582311189248008, 360582310936249537, 360582310682956385, 360582310626203946, 360582310447076259, 360582310067931604, 360582309688604201, 360582309460824859, 360582309373751283, 360582309291886505]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk712B
