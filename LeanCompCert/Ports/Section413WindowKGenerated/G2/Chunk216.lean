import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk216

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578118283614582, 360578121010191627⟩, ⟨39256101917042769, 39295951890941091⟩, true⟩

def state01 : KState := ⟨⟨360569692727226074, 360569695456432707⟩, ⟨221494527806475939, 221534434592476673⟩, true⟩

def words00 : List Nat := [360579942234248057, 360579944369179451, 360579945167657348, 360579945966093107, 360579945966326767, 360579946727110183, 360579947344824627, 360579947962534431, 360579947962789445, 360579946934201910]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360669576543613787, 360669579275452141⟩, ⟨(-1937463578904540608), (-1937423615233779728)⟩, true⟩

def words01 : List Nat := [360579948119675872, 360579949779441344, 360579953572707328, 360579956011736583, 360579956312190338, 360579956612641307, 360579959046037723, 360579962566705627, 360579966712016175, 360579970857005549]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360654347638967346, 360654350373466199⟩, ⟨(-1608568277892708734), (-1608528256689019642)⟩, true⟩

def words02 : List Nat := [360579973927775631, 360579976153535861, 360579978318008361, 360579980482358993, 360579981998195894, 360579983231935524, 360579983303153958, 360579983374393780, 360579984757947039, 360579988196188726]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360553751293091706, 360553754030217737⟩, ⟨568099411645995815, 568139489689078393⟩, true⟩

def words03 : List Nat := [360579993001195588, 360579997805812780, 360580001538362260, 360580004220637126, 360580006362019114, 360580008503279489, 360580009520953337, 360580009521232855, 360580009378590397, 360580008165600782]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360619328348225373, 360619331087988561⟩, ⟨(-851559527586267970), (-851519392462165198)⟩, true⟩

def words04 : List Nat := [360580006952661496, 360580005242093611, 360580004928815571, 360580005251283473, 360580005251544604, 360580003573863763, 360580000538579170, 360579999629771415, 360579999937931859, 360580001754818631]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360625901683899185, 360625904426327861⟩, ⟨(-994026944723780702), (-993986751879016414)⟩, true⟩

def words05 : List Nat := [360580001928180872, 360580002101553458, 360580003620684081, 360580006228969258, 360580007822270472, 360580009415469999, 360580009939351047, 360580011875253480, 360580013994250902, 360580016113143843]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360629928459374336, 360629931204433113⟩, ⟨(-1081417073952057550), (-1081376824126193254)⟩, true⟩

def words06 : List Nat := [360580020355455391, 360580022478298545, 360580023247141662, 360580024015941840, 360580024016179939, 360580024039211302, 360580026162484983, 360580028285615972, 360580029181800996, 360580031484801985]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360634160855535217, 360634163603237082⟩, ⟨(-1173110629707589655), (-1173070322593000555)⟩, true⟩

def words07 : List Nat := [360580034412500640, 360580037340017741, 360580042388638365, 360580045319090065, 360580046198792368, 360580047078434520, 360580049351887736, 360580052697112584, 360580055193233872, 360580057689183626]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360633663687920912, 360633666438289016⟩, ⟨(-1162635601253537410), (-1162595236321880628)⟩, true⟩

def words08 : List Nat := [360580058558769372, 360580058559049384, 360580060124144643, 360580061966567938, 360580063269388435, 360580064647069334, 360580064958721916, 360580065270376376, 360580065919925865, 360580068391342270]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360548685253102320, 360548688006111291⟩, ⟨681117775273396217, 681158197498605257⟩, true⟩

def words09 : List Nat := [360580072510157890, 360580076628649967, 360580079114561786, 360580079487042151, 360580079487276602, 360580079322045445, 360580079617424943, 360580079617705576, 360580079231102942, 360580077784797863]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk216
