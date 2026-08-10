import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk815A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360609395783553177, 360609439109864346⟩, ⟨(-2218674808788726832), (-2216290040691452446)⟩, true⟩

def state01 : KState := ⟨⟨360601023569840598, 360601066907285124⟩, ⟨(-1536434978342809950), (-1534049302824601812)⟩, true⟩

def words00 : List Nat := [360582245919810167, 360582245988875783, 360582246174380668, 360582246360235689, 360582246508113452, 360582246541538325, 360582246542578408, 360582246486859258, 360582246524352390, 360582246756595959]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 81500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 81500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574520395761013, 360574563744181929⟩, ⟨624020829472401206, 626407399732344588⟩, true⟩

def words01 : List Nat := [360582247075133719, 360582247393888578, 360582247637100634, 360582247778152803, 360582247779149589, 360582247779881530, 360582247930044293, 360582247931211836, 360582247931932060, 360582247838879333]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 81510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 81500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580221327672593, 360580264687130502⟩, ⟨159272309529566750, 161659779579204722⟩, true⟩

def words02 : List Nat := [360582247745570527, 360582247719557915, 360582247809416143, 360582247899491518, 360582247900569639, 360582247863389687, 360582247675918237, 360582247639085736, 360582247601929303, 360582247512833669]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 81520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 81500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360581169172897970, 360581212543487084⟩, ⟨81997634397776493, 84386012028786527⟩, true⟩

def words03 : List Nat := [360582247489563850, 360582247390854958, 360582247342306270, 360582247479535280, 360582247536497976, 360582247593674753, 360582247594715141, 360582247576585388, 360582247458095890, 360582247446749640]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 81530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 81500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360578485849475124, 360578529231081735⟩, ⟨300750886883078964, 303140162934486718⟩, true⟩

def words04 : List Nat := [360582247536017280, 360582247537185149, 360582247489242383, 360582247298341484, 360582247107255104, 360582246852464457, 360582246672723133, 360582246643435524, 360582246614035167, 360582246461773759]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 81540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 81500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk815A
