import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk865A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360558517205520190, 360558566236907137⟩, ⟨2042105275705835599, 2044969421419947125⟩, true⟩

def state01 : KState := ⟨⟨360593796382317123, 360593845425449506⟩, ⟨(-1009720797869709871), (-1006855636118530159)⟩, true⟩

def words00 : List Nat := [360582207229593914, 360582207091198688, 360582207041262427, 360582207048563855, 360582207049711534, 360582206942688838, 360582206878805635, 360582206815327473, 360582206820113729, 360582206955935589]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 86500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 86500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574059520955274, 360574108575949517⟩, ⟨697786223919908513, 700652411899490759⟩, true⟩

def words01 : List Nat := [360582207024707311, 360582207093613243, 360582207105186852, 360582207184453565, 360582207185506967, 360582207154837620, 360582207124043167, 360582207026552302, 360582206823582201, 360582206731426858]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 86510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 86500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360568468221416044, 360568517288130464⟩, ⟨1181537198417106437, 1184404400483551849⟩, true⟩

def words02 : List Nat := [360582206638835861, 360582206628050689, 360582206483589476, 360582206263616158, 360582206043446019, 360582205788807849, 360582205649768492, 360582205481270957, 360582205312635610, 360582205077342108]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 86520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 86500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601393019557966, 360601442098006434⟩, ⟨(-1667608668423796348), (-1664740450949710346)⟩, true⟩

def words03 : List Nat := [360582204920164390, 360582204896791519, 360582204981742802, 360582205097432451, 360582205099578709, 360582205101810914, 360582205124393370, 360582205214641668, 360582205437936536, 360582205661508708]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 86530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 86500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575226764486708, 360575275854810164⟩, ⟨596862531711090774, 599731776904117420⟩, true⟩

def words04 : List Nat := [360582205776600210, 360582205777844860, 360582205816991908, 360582205876045572, 360582205877089428, 360582205872617352, 360582205763204975, 360582205561581640, 360582205359695940, 360582205164768618]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 86540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 86500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk865A
