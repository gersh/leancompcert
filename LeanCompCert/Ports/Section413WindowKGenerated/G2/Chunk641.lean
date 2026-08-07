import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk641

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360633212937526583, 360633239234021260⟩, ⟨(-3230296816881057950), (-3229158159093203600)⟩, true⟩

def state01 : KState := ⟨⟨360631776884700241, 360631803189780557⟩, ⟨(-3138429092050413383), (-3137289883879977665)⟩, true⟩

def words00 : List Nat := [360582863768109317, 360582864156508123, 360582864615735601, 360582865075209771, 360582865472921441, 360582865960553459, 360582866273715097, 360582866586962743, 360582867143144967, 360582867907475181]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 64100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 64100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591805273049949, 360591831586634708⟩, ⟨(-575568963377891588), (-574429209945657974)⟩, true⟩

def words01 : List Nat := [360582868843473680, 360582869779615589, 360582870504282935, 360582870986839736, 360582871407786081, 360582871828972317, 360582872428605567, 360582872786235812, 360582872926764923, 360582873067429680]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 64110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 64100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611001494415202, 360611027816513776⟩, ⟨(-1806493193198741016), (-1805352893819809358)⟩, true⟩

def words02 : List Nat := [360582873349649848, 360582873753498708, 360582874400057496, 360582875046772975, 360582875492508676, 360582875696189074, 360582875893440829, 360582876090938362, 360582876359253207, 360582876799161485]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 64120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 64100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360604828963766719, 360604855294444071⟩, ⟨(-1410592075017030265), (-1409451225436911325)⟩, true⟩

def words03 : List Nat := [360582877116694065, 360582877434315183, 360582877915056554, 360582878583160003, 360582879144937522, 360582879706844647, 360582880146456934, 360582880344128999, 360582880687468222, 360582881031095559]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 64130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 64100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587919192449309, 360587945531636342⟩, ⟨(-326004662611475882), (-324863267177833972)⟩, true⟩

def words04 : List Nat := [360582881187313440, 360582881271465326, 360582881272276708, 360582881235272342, 360582881198120045, 360582881121830663, 360582881258902030, 360582881396157449, 360582881411181755, 360582881491057430]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 64140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 64100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk641
