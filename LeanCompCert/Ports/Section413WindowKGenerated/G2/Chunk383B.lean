import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk383A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk383B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk383A

def state06 : KState := ⟨⟨360672940441807240, 360672949474823924⟩, ⟨(-3487190845708524526), (-3486956630102265652)⟩, true⟩

def words05 : List Nat := [360582032881347170, 360582035407029205, 360582037913778936, 360582039944853101, 360582041397514704, 360582042850141395, 360582044379254120, 360582046253491470, 360582048623650244, 360582050993811900]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360600606224095364, 360600615262043907⟩, ⟨(-712244474983852902), (-712010070166954518)⟩, true⟩

def words06 : List Nat := [360582052956259753, 360582054243687982, 360582055668896888, 360582057094181995, 360582058347299261, 360582058925532593, 360582058930718064, 360582058935950200, 360582058936370596, 360582059319530891]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597610870434964, 360597619913262600⟩, ⟨(-597146889597566257), (-596912297545558619)⟩, true⟩

def words07 : List Nat := [360582060481312572, 360582061643133055, 360582062464242734, 360582063301241268, 360582063939946531, 360582064578763214, 360582065894966110, 360582066815578718, 360582067221283004, 360582067627039064]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360636611882162039, 360636620929887998⟩, ⟨(-2094260034896017426), (-2094025254821754354)⟩, true⟩

def words08 : List Nat := [360582068014210053, 360582068738740837, 360582069990764160, 360582071242821491, 360582071908346877, 360582072346373662, 360582073102947441, 360582073859642770, 360582074816953483, 360582076238298257]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360611511222041789, 360611520274697261⟩, ⟨(-1130436420323468221), (-1130201450980091115)⟩, true⟩

def words09 : List Nat := [360582077241735075, 360582078245176340, 360582079925433863, 360582081975734357, 360582083563139507, 360582085150539606, 360582086397630296, 360582087177745602, 360582087944652979, 360582088711691608]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk383B
