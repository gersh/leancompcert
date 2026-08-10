import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk641A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk641B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk641A

def state06 : KState := ⟨⟨360629814790659279, 360629841138364911⟩, ⟨(-3013856077376112415), (-3012714135433881619)⟩, true⟩

def words05 : List Nat := [360582881813454924, 360582882136124008, 360582882701223603, 360582883024584397, 360582883132512548, 360582883240489324, 360582883590992877, 360582884137130389, 360582884869733750, 360582885602518620]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 64150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 64100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360597235474121836, 360597261830442877⟩, ⟨(-923465504421047181), (-922323009673214341)⟩, true⟩

def words06 : List Nat := [360582886214137191, 360582886832174979, 360582887386818257, 360582887941702466, 360582888378979640, 360582888574584673, 360582888640158814, 360582888705833537, 360582888710971216, 360582888935994089]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 64160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 64100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577649464751131, 360577675829570143⟩, ⟨333571589409701322, 334714629516072882⟩, true⟩

def words07 : List Nat := [360582889403320895, 360582889870806111, 360582890216094472, 360582890523409687, 360582890677018184, 360582890830875357, 360582891114856391, 360582891157284502, 360582891158097219, 360582891077770768]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 64170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 64100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360604601777812197, 360604628151165674⟩, ⟨(-1396462171370099008), (-1395318583479393146)⟩, true⟩

def words08 : List Nat := [360582890997245902, 360582891130073461, 360582891215789829, 360582891301663638, 360582891302502024, 360582891149568191, 360582890827295904, 360582890747798691, 360582890830016878, 360582891169603160]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 64180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 64100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588695130992372, 360588721512944564⟩, ⟨(-375311026610136214), (-374166886725015768)⟩, true⟩

def words09 : List Nat := [360582891387051536, 360582891604594201, 360582891936302031, 360582892425008986, 360582892792136375, 360582893159405270, 360582893338334163, 360582893339237373, 360582893367260273, 360582893459071182]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 64190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 64100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 64100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk641B
