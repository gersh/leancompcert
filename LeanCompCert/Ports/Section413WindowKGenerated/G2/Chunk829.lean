import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk829

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589064388458275, 360589109275529173⟩, ⟨(-558383080307002379), (-555870014566866081)⟩, true⟩

def state01 : KState := ⟨⟨360590536848001578, 360590581746308038⟩, ⟨(-680453997084303083), (-677939999860786089)⟩, true⟩

def words00 : List Nat := [360582404069966732, 360582404185479996, 360582404446092342, 360582404706926716, 360582404843986988, 360582404845175713, 360582404849946540, 360582404864259968, 360582404926842479, 360582405026694709]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360592610668575726, 360592655578199131⟩, ⟨(-852424397413333573), (-849909461846369741)⟩, true⟩

def words01 : List Nat := [360582405035605022, 360582405044643914, 360582405198872941, 360582405444976100, 360582405562271862, 360582405679742555, 360582405700986574, 360582405702183585, 360582405824529137, 360582405949494143]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593480599518800, 360593525520356325⟩, ⟨(-924526904465088365), (-922011038967084161)⟩, true⟩

def words02 : List Nat := [360582406181783378, 360582406417605398, 360582406570969497, 360582406724459601, 360582406813496358, 360582407005932282, 360582407241660566, 360582407477606789, 360582407575812054, 360582407711105658]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360620034019112639, 360620078951174067⟩, ⟨(-3126781705343331439), (-3124264908992343269)⟩, true⟩

def words03 : List Nat := [360582407962526891, 360582408214291313, 360582408582253074, 360582408805419290, 360582408899277718, 360582408993234296, 360582409208123492, 360582409518312456, 360582409973450721, 360582410428863119]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597603159911890, 360597648103306549⟩, ⟨(-1266395396998829234), (-1263877660614896272)⟩, true⟩

def words04 : List Nat := [360582410811091202, 360582411078851508, 360582411255819340, 360582411433126009, 360582411551535374, 360582411568615890, 360582411569675984, 360582411501178387, 360582411481543168, 360582411666607596]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk829
