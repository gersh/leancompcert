import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk931

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590686660316756, 360590743784501004⟩, ⟨(-814931519760085283), (-811340286497447597)⟩, true⟩

def state01 : KState := ⟨⟨360608450774483240, 360608507911379755⟩, ⟨(-2468805850550075640), (-2465213433711593566)⟩, true⟩

def words00 : List Nat := [360582029345512752, 360582029603420060, 360582029976211339, 360582030349264062, 360582030623291459, 360582030863463192, 360582031080772591, 360582031298453768, 360582031554773457, 360582031840521193]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594155230953742, 360594212380681283⟩, ⟨(-1137617470648326781), (-1134023859048605667)⟩, true⟩

def words01 : List Nat := [360582032054058527, 360582032267738067, 360582032596419421, 360582033014408852, 360582033357424981, 360582033700646026, 360582033985766839, 360582034155995868, 360582034287873791, 360582034420188499]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586756225087683, 360586813387522712⟩, ⟨(-448646078604409112), (-445051283622190618)⟩, true⟩

def words02 : List Nat := [360582034524083984, 360582034543238701, 360582034544451839, 360582034504656709, 360582034464642888, 360582034408850490, 360582034486741354, 360582034564910903, 360582034568521258, 360582034621229833]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360606834087563692, 360606891262717488⟩, ⟨(-2318612722404003575), (-2315016742859809545)⟩, true⟩

def words03 : List Nat := [360582034788855535, 360582034956894680, 360582035239735126, 360582035407833740, 360582035467245834, 360582035526739941, 360582035603558071, 360582035756706640, 360582036024658121, 360582036292909780]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591058450918337, 360591115638944042⟩, ⟨(-849234860544229216), (-845637682050242628)⟩, true⟩

def words04 : List Nat := [360582036492871510, 360582036695943558, 360582036937772724, 360582037179989729, 360582037357449401, 360582037420154722, 360582037421356028, 360582037416532447, 360582037411459391, 360582037500415736]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360577839023283429, 360577896224006547⟩, ⟨382277947623216513, 385876308945096185⟩, true⟩

def words05 : List Nat := [360582037714140790, 360582037928120476, 360582038084045228, 360582038162945162, 360582038192241897, 360582038221920629, 360582038301473935, 360582038347309973, 360582038348530708, 360582038305467959]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360604093758755565, 360604150972215421⟩, ⟨(-2063803913564580198), (-2060204365623599014)⟩, true⟩

def words06 : List Nat := [360582038295706396, 360582038388280330, 360582038477840208, 360582038567637605, 360582038568881205, 360582038560701681, 360582038503699519, 360582038522505479, 360582038656031434, 360582038894791936]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360595347775122807, 360595405001414930⟩, ⟨(-1248898799842745264), (-1245298056255635078)⟩, true⟩

def words07 : List Nat := [360582039061082164, 360582039227510316, 360582039448100276, 360582039733961604, 360582039989981492, 360582040246217559, 360582040390657683, 360582040420327011, 360582040564844695, 360582040709807675]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588634934261834, 360588692173248197⟩, ⟨(-623433872146100739), (-619831945643794669)⟩, true⟩

def words08 : List Nat := [360582040838465257, 360582040852498814, 360582040853700428, 360582040801982795, 360582040750016163, 360582040669509475, 360582040755833406, 360582040857343099, 360582040900839513, 360582040973608277]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360601742290393243, 360601799542135133⟩, ⟨(-1845034890454848503), (-1841431775204178267)⟩, true⟩

def words09 : List Nat := [360582041043467073, 360582041113711556, 360582041252063882, 360582041351480952, 360582041359714508, 360582041368040300, 360582041377534467, 360582041475985019, 360582041689071784, 360582041902461695]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk931
