import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk865

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

def state06 : KState := ⟨⟨360552648549661801, 360552697651697773⟩, ⟨2551179325758218880, 2554049584728596748⟩, true⟩

def words05 : List Nat := [360582205085714849, 360582205086391126, 360582205086941332, 360582205000754917, 360582204876225444, 360582204661236273, 360582204445886469, 360582204330352937, 360582204109410579, 360582203769820793]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360569840813988037, 360569889927799047⟩, ⟨1062998791859702812, 1065870070133520450⟩, true⟩

def words06 : List Nat := [360582203429956383, 360582203223850146, 360582203129656225, 360582203136088734, 360582203137238171, 360582203030708674, 360582202790548331, 360582202590369902, 360582202389848117, 360582202161484314]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360576875847809198, 360576924973480072⟩, ⟨453936456954562508, 456808761994620896⟩, true⟩

def words07 : List Nat := [360582202020382956, 360582201812679955, 360582201604741333, 360582201532576610, 360582201533619956, 360582201502284624, 360582201470792517, 360582201372683582, 360582201179455897, 360582201119957257]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360569406518500249, 360569455655910639⟩, ⟨1100555249581027815, 1103428571087394401⟩, true⟩

def words08 : List Nat := [360582201060034683, 360582200958644546, 360582200723784399, 360582200386568390, 360582200049156862, 360582199678412593, 360582199374543014, 360582199204187305, 360582199033711280, 360582198796817065]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582173297778643, 360582222446944403⟩, ⟨(-5012140173161577), (-2137800711471343)⟩, true⟩

def words09 : List Nat := [360582198650659094, 360582198612735334, 360582198574762661, 360582198576009241, 360582198506440631, 360582198310813037, 360582198114968995, 360582197891388098, 360582197759732890, 360582197761309001]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk865
