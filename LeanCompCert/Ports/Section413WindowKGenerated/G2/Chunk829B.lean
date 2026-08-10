import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk829A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk829B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk829A

def state06 : KState := ⟨⟨360569593057674161, 360569638012264866⟩, ⟨1057235956740334510, 1059754621892228542⟩, true⟩

def words05 : List Nat := [360582411873438946, 360582412080486742, 360582412195181111, 360582412324666290, 360582412393766511, 360582412463181311, 360582412528058272, 360582412529247812, 360582412449269138, 360582412296521041]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 82950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 82900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602192540145506, 360602237505962858⟩, ⟨(-1647363901173056070), (-1644844304601713910)⟩, true⟩

def words06 : List Nat := [360582412143504647, 360582412085499475, 360582412258222576, 360582412431190218, 360582412480616645, 360582412488025302, 360582412611320044, 360582412734961244, 360582412937964975, 360582413178130222]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 82960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 82900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587848361171918, 360587893338346632⟩, ⟨(-457191228189140363), (-454670689241638139)⟩, true⟩

def words07 : List Nat := [360582413305180961, 360582413432328783, 360582413522641287, 360582413685925348, 360582413810621435, 360582413935507479, 360582413960846283, 360582413989558137, 360582414056556700, 360582414123957295]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 82970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 82900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585977781002583, 360586022769368872⟩, ⟨(-301985115968067104), (-299463648286485082)⟩, true⟩

def words08 : List Nat := [360582414336109775, 360582414403650428, 360582414404710573, 360582414397849704, 360582414390801983, 360582414284615188, 360582414303140685, 360582414356796274, 360582414357866433, 360582414382335502]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 82980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 82900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603407112004548, 360603452111628621⟩, ⟨(-1748527296955596052), (-1746004894937364488)⟩, true⟩

def words09 : List Nat := [360582414510709049, 360582414639460540, 360582414880164930, 360582415071790931, 360582415120487415, 360582415169267828, 360582415362921185, 360582415652411151, 360582415906841487, 360582416161520341]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 82990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 82900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 82900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk829B
