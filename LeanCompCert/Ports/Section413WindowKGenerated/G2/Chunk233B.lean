import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk233A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk233B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk233A

def state06 : KState := ⟨⟨360656381605566819, 360656384816774090⟩, ⟨(-1760132827753042607), (-1760082077265667903)⟩, true⟩

def words05 : List Nat := [360581018118705473, 360581021967776955, 360581025969848618, 360581028153461521, 360581028767420388, 360581029381347525, 360581031824487005, 360581035611309781, 360581038837125057, 360581042062728216]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360663832321960432, 360663835536058796⟩, ⟨(-1934719992992336295), (-1934669174954887455)⟩, true⟩

def words06 : List Nat := [360581044094787253, 360581044309241859, 360581045741028340, 360581047172785987, 360581048136128308, 360581049143041265, 360581049230258392, 360581049317501499, 360581051232119690, 360581054774647009]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360610732301165349, 360610735518128195⟩, ⟨(-693237590059090114), (-693186705064492506)⟩, true⟩

def words07 : List Nat := [360581060144055059, 360581065513061547, 360581069439037136, 360581073812526436, 360581076584265042, 360581079355843934, 360581083358178928, 360581085545123958, 360581086813571435, 360581088081959319]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360658311242138104, 360658314461967678⟩, ⟨(-1805715483970938840), (-1805664531937854654)⟩, true⟩

def words08 : List Nat := [360581090605473316, 360581094073449036, 360581098746059433, 360581103418328279, 360581106534761496, 360581109389158959, 360581111441173216, 360581113493095256, 360581116320056910, 360581119620706601]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360652249958031828, 360652253180759632⟩, ⟨(-1663903426764074343), (-1663852406927291023)⟩, true⟩

def words09 : List Nat := [360581121776704973, 360581123932550162, 360581127366824108, 360581132253165027, 360581136672656585, 360581141091819826, 360581144120836263, 360581145337650502, 360581148376693346, 360581151415581764]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk233B
