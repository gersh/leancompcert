import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk698A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk698B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk698A

def state06 : KState := ⟨⟨360578883011751951, 360578914461530352⟩, ⟨256338872957343763, 257822925985123049⟩, true⟩

def words05 : List Nat := [360582607770840716, 360582607614500709, 360582607457891217, 360582607209056175, 360582606820540282, 360582606257416245, 360582605694118253, 360582605335524280, 360582605079106096, 360582605027318860]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 69850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 69800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566681944190136, 360566713403385197⟩, ⟨1108634554568142752, 1110119265489346540⟩, true⟩

def words06 : List Nat := [360582604975379675, 360582604752683146, 360582604470660945, 360582604279339024, 360582604087760029, 360582603810822172, 360582603372952234, 360582602779007213, 360582602184889855, 360582601756977431]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 69860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 69800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561327167681287, 360561358636192012⟩, ⟨1482879972384192671, 1484365334237285279⟩, true⟩

def words07 : List Nat := [360582601530381756, 360582601468197928, 360582601405901386, 360582601241494100, 360582601170703121, 360582600970289114, 360582600772337221, 360582600773326546, 360582600572434300, 360582600269481041]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 69870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 69800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566945036411227, 360566976514275999⟩, ⟨1090216814680715585, 1091702830241622591⟩, true⟩

def words08 : List Nat := [360582599966326397, 360582599604598558, 360582599368391409, 360582599164506079, 360582598960558238, 360582598582390962, 360582598053142591, 360582597594355716, 360582597135267722, 360582596815180873]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 69880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 69800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360560087993329504, 360560119480609127⟩, ⟨1569492635046705930, 1570979308658887212⟩, true⟩

def words09 : List Nat := [360582596592567340, 360582596267931159, 360582595943115118, 360582595738081243, 360582595691946529, 360582595503199743, 360582595314351779, 360582594994097638, 360582594469230814, 360582594148830285]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 69890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 69800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 69800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk698B
