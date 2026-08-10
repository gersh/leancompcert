import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk450A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk450B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk450A

def state06 : KState := ⟨⟨360598804443666428, 360598817072820765⟩, ⟨(-701584245492532944), (-701199685176750590)⟩, true⟩

def words05 : List Nat := [360583249791005739, 360583250154458608, 360583251009714754, 360583252112480978, 360583253089907423, 360583254067395129, 360583254735297053, 360583255259648646, 360583255605513728, 360583255951558993]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 45050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 45000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588986759513199, 360588999394472738⟩, ⟨(-259136609079730948), (-258751787152332564)⟩, true⟩

def words06 : List Nat := [360583256789195797, 360583257135734596, 360583257237543405, 360583257339409620, 360583257339925812, 360583257750630565, 360583258016504611, 360583258282481541, 360583258284733977, 360583258412751624]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 45060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 45000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611739414933997, 360611752055724930⟩, ⟨(-1284866804815040174), (-1284481720038023366)⟩, true⟩

def words07 : List Nat := [360583258682822667, 360583258953066398, 360583259098111906, 360583259098729310, 360583258958117347, 360583258390669758, 360583257823129186, 360583258039179245, 360583258671754902, 360583259304454151]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 45070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 45000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574046627237678, 360574059273908408⟩, ⟨414392931547124517, 414778281413667239⟩, true⟩

def words08 : List Nat := [360583259689663881, 360583259690280882, 360583259970006506, 360583260355974076, 360583260527664157, 360583260528281216, 360583260209339874, 360583259504582647, 360583258799741975, 360583258171256239]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 45080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 45000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360542001347156881, 360542013999636892⟩, ⟨1859613934300290282, 1859999546136888594⟩, true⟩

def words09 : List Nat := [360583258112034617, 360583258256932004, 360583258257481883, 360583258155401257, 360583258069393370, 360583257750700021, 360583257431842410, 360583257255426072, 360583256588543209, 360583255674717533]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 45090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 45000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 45000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk450B
