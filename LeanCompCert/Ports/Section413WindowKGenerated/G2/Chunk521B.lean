import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk521A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk521B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk521A

def state06 : KState := ⟨⟨360610933845647365, 360610950972401375⟩, ⟨(-1510265902037289239), (-1509662294720651635)⟩, true⟩

def words05 : List Nat := [360582005173255599, 360582005540701992, 360582006274971482, 360582006740351122, 360582006890131903, 360582007039961019, 360582007179121375, 360582007504079768, 360582008059561724, 360582008615185819]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 52150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 52100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608152702110385, 360608169835742295⟩, ⟨(-1365272459576800422), (-1364668493475609018)⟩, true⟩

def words06 : List Nat := [360582008986564706, 360582009304425501, 360582009989017134, 360582010673817563, 360582011266399155, 360582011492468605, 360582011534413628, 360582011576435901, 360582011726934795, 360582012229150978]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 52160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 52100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581641706865423, 360581658847306976⟩, ⟨17868776408592822, 18473097803339310⟩, true⟩

def words07 : List Nat := [360582012605280331, 360582012981523044, 360582013034128569, 360582013034852611, 360582012932149811, 360582012733268859, 360582012701201787, 360582012879105079, 360582012879748767, 360582012873711793]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 52170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 52100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360641534134932073, 360641551282192776⟩, ⟨(-3107603489613644936), (-3106998812362105650)⟩, true⟩

def words08 : List Nat := [360582013227354238, 360582013840210804, 360582014819433966, 360582015798762865, 360582016426103772, 360582016807037063, 360582017358036798, 360582017909226575, 360582018826712764, 360582019968127859]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 52180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 52100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593257984790308, 360593275138948151⟩, ⟨(-587779657161329875), (-587174619914244615)⟩, true⟩

def words09 : List Nat := [360582020923229223, 360582021878378832, 360582022813827759, 360582023934546047, 360582024740472894, 360582025546479867, 360582026139302095, 360582026366089278, 360582026582177529, 360582026798496546]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 52190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 52100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 52100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk521B
