import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk216A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk216A
