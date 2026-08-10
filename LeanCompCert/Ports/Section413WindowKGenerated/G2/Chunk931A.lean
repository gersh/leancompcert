import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk931A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk931A
