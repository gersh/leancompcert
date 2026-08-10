import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk664A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk664B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk664A

def state06 : KState := ⟨⟨360538794205609398, 360538822555992420⟩, ⟨2929808099115611327, 2931080850257648675⟩, true⟩

def words05 : List Nat := [360582931344966004, 360582930878010393, 360582930410968470, 360582929786146949, 360582929000527374, 360582928158561512, 360582927316331419, 360582926700271941, 360582926150475901, 360582925487834997]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580403689652935, 360580432048885447⟩, ⟨164240549391837124, 165513888712443742⟩, true⟩

def words06 : List Nat := [360582924825002042, 360582924298793694, 360582923957213233, 360582923841726820, 360582923726193348, 360582923395001074, 360582922885632109, 360582922602437469, 360582922318979019, 360582922102875405]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561687268952318, 360561715637117272⟩, ⟨1408440684701695780, 1409714617807324306⟩, true⟩

def words07 : List Nat := [360582922066249884, 360582921916797130, 360582921767158175, 360582921652597721, 360582921652788963, 360582921593507556, 360582921534125740, 360582921361946912, 360582921048551295, 360582920730646264]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360564303174635194, 360564331551629344⟩, ⟨1234505504646301759, 1235780024761441229⟩, true⟩

def words08 : List Nat := [360582920412441208, 360582920193035201, 360582919907595363, 360582919493921634, 360582919080101167, 360582918610005526, 360582918313587019, 360582918094134244, 360582917874586307, 360582917504776606]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574464705885638, 360574493091746823⟩, ⟨558746577705688630, 560021687432320802⟩, true⟩

def words09 : List Nat := [360582917226008894, 360582917173218814, 360582917120160283, 360582916966070195, 360582916586259528, 360582915999357906, 360582915412295039, 360582914947678640, 360582914596153334, 360582914470505204]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk664B
