import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk073

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362366385351056386, 362366386002020849⟩, ⟨874507272656259529, 874510490814657795⟩, true⟩

def state01 : KState := ⟨⟨362521524423588562, 362521525076412550⟩, ⟨(-258969271210732338), (-258966039468416966)⟩, true⟩

def words00 : List Nat := [371286165551652701, 371286155704004902, 371286136485429955, 371286132418904184, 371286128353424576, 371286121368258167, 371286097076979599, 371286091438160362, 371286098805408051, 371286103651235637]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 7300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 7300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362467386636441798, 362467387291159177⟩, ⟨137415673244246810, 137418918836867860⟩, true⟩

def words01 : List Nat := [371286108557721320, 371286113462937234, 371286133221198130, 371286145765739891, 371286156313343795, 371286166858138202, 371286177286818327, 371286177287026372, 371286162932222850, 371286160367503012]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 7310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 7300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362455754423387137, 362455755079961430⟩, ⟨223257382460529289, 223260641655477729⟩, true⟩

def words02 : List Nat := [371286173799275671, 371286174457992217, 371286175209382854, 371286175960636165, 371286182569130917, 371286182783088965, 371286194410278154, 371286206034380764, 371286213557461568, 371286213557677048]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 7320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 7300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362615724464924248, 362615725123379864⟩, ⟨(-949672920186673935), (-949669647191915391)⟩, true⟩

def words03 : List Nat := [371286223763925472, 371286238121113582, 371286270983729760, 371286285205213608, 371286296049864894, 371286306891628593, 371286320445317167, 371286324707800544, 371286342337426955, 371286359962340236]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 7330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 7300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362447720540464569, 362447721200807988⟩, ⟨283668182675428175, 283671469536042045⟩, true⟩

def words04 : List Nat := [371286377661253461, 371286377661462237, 371286371447805168, 371286372159587847, 371286376737074970, 371286376737283845, 371286356721233927, 371286336984445075, 371286317252943757, 371286315958567994]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 7340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 7300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362333918567986862, 362333919230212457⟩, ⟨1121429639711985038, 1121432940416350000⟩, true⟩

def words05 : List Nat := [371286323886255436, 371286337060717675, 371286349428103934, 371286349428312959, 371286337244378720, 371286330515946184, 371286324699881129, 371286324700091239, 371286308541079024, 371286287836247288]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 7350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 7300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362496750856480811, 362496751520579233⟩, ⟨(-77871431939046282), (-77868117440976880)⟩, true⟩

def words06 : List Nat := [371286267136946183, 371286257819294923, 371286239574218806, 371286235692326826, 371286231811422519, 371286225066175552, 371286199423578101, 371286188826358522, 371286185968469473, 371286187402082289]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 7360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 7300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362573630901905105, 362573631567915316⟩, ⟨(-645001226350873354), (-644997897753300650)⟩, true⟩

def words07 : List Nat := [371286187402244217, 371286186001935255, 371286197801238317, 371286201800937539, 371286209273798575, 371286216744715708, 371286224288781027, 371286224288995095, 371286233478529845, 371286245319743890]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 7370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 7300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362397067862552359, 362397068530430636⟩, ⟨658845664743143104, 658849007136939432⟩, true⟩

def words08 : List Nat := [371286264516491081, 371286264516701033, 371286259362691126, 371286252462016617, 371286245563130954, 371286239305635645, 371286223882202499, 371286223568058231, 371286223253932012, 371286222658595310]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 7380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 7300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479805160918510, 362479805830704069⟩, ⟨47313101630562768, 47316458128418564⟩, true⟩

def words09 : List Nat := [371286211663597717, 371286212730953391, 371286231995819361, 371286231996029650, 371286226987383931, 371286216906035121, 371286208267598609, 371286208267832407, 371286200810615910, 371286199946667369]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 7390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 7300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 7300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk073
