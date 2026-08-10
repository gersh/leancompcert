import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk865A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk865B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk865A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk865B
