import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk532A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk532B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk532A

def state06 : KState := ⟨⟨360582607408426012, 360582625295499773⟩, ⟨(-34463355952062160), (-33819670669777768)⟩, true⟩

def words05 : List Nat := [360581986981972856, 360581987944943950, 360581988669860718, 360581989043248852, 360581989328121867, 360581989613193865, 360581990054598118, 360581990290215552, 360581990302796371, 360581990315483068]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 53250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 53200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360607309548493856, 360607327442549508⟩, ⟨(-1350354901760620242), (-1349710844589018206)⟩, true⟩

def words06 : List Nat := [360581990316084637, 360581990467902968, 360581990667255423, 360581990866731352, 360581990867412605, 360581990749011082, 360581990279054219, 360581990161006131, 360581990275550755, 360581990751956334]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 53260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 53200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596403953849092, 360596421854946133⟩, ⟨(-769418949870306821), (-768774517569634399)⟩, true⟩

def words07 : List Nat := [360581991047274923, 360581991342656453, 360581991557118486, 360581991991322512, 360581992333555670, 360581992675897412, 360581992711511763, 360581992712252660, 360581992902939784, 360581993174599112]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 53270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 53200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594031079583912, 360594048987634259⟩, ⟨(-642991520549175853), (-642346717740746333)⟩, true⟩

def words08 : List Nat := [360581993797526460, 360581994069325528, 360581994164737869, 360581994260245255, 360581994267342762, 360581994470498800, 360581994778759564, 360581995087147515, 360581995192203441, 360581995419156641]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 53280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 53200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360611946632076504, 360611964547118104⟩, ⟨(-1597965239960959313), (-1597320064555953943)⟩, true⟩

def words09 : List Nat := [360581995520301354, 360581995621647791, 360581995998723518, 360581996024792535, 360581996025481913, 360581995691256892, 360581995356902889, 360581995501967936, 360581996064836693, 360581996627856628]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 53290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 53200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 53200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk532B
