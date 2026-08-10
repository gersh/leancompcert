import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk826A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485082016153766, 362485184576183910⟩, ⟨1596121223393571, 7316344841361869⟩, true⟩

def state01 : KState := ⟨⟨362494210612654011, 362494313198300132⟩, ⟨(-752447190649118325), (-746724851018187157)⟩, true⟩

def words00 : List Nat := [371285273298228813, 371285273392144266, 371285273556335294, 371285273721655541, 371285273862521249, 371285273865384347, 371285273846261960, 371285273869186528, 371285274037211518, 371285274149613902]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498960393216809, 362499063004932619⟩, ⟨(-1144840557077239731), (-1139116063702505259)⟩, true⟩

def words01 : List Nat := [371285274247780175, 371285274346870924, 371285274591425331, 371285274786601335, 371285274989540739, 371285275193590013, 371285275396377492, 371285275419529767, 371285275588351330, 371285275758788146]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484377414038016, 362484480051288893⟩, ⟨60049046391355058, 65775649605051000⟩, true⟩

def words02 : List Nat := [371285275910256443, 371285275913120116, 371285275887160655, 371285275861956229, 371285275853951939, 371285275857108822, 371285275901532773, 371285275988633151, 371285276074581018, 371285276077545762]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362497876906871601, 362497979570026319⟩, ⟨(-1055469978173876852), (-1049741234394438466)⟩, true⟩

def words03 : List Nat := [371285276168188095, 371285276269991318, 371285276516793651, 371285276587472114, 371285276620378429, 371285276654111345, 371285276778346967, 371285276830831876, 371285276986489050, 371285277143453620]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488727723750314, 362488830412759108⟩, ⟨(-299358030172465201), (-293627149680944517)⟩, true⟩

def words04 : List Nat := [371285277293145865, 371285277322298194, 371285277426840138, 371285277532821043, 371285277682190909, 371285277685058591, 371285277686973057, 371285277690044084, 371285277751889109, 371285277798154555]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk826A
