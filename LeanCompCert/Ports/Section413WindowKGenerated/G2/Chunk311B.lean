import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk311A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk311B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk311A

def state06 : KState := ⟨⟨360616492898374149, 360616498757180076⟩, ⟨(-1047589089122150621), (-1047465633383927089)⟩, true⟩

def words05 : List Nat := [360582882023592878, 360582881970126509, 360582882888802977, 360582883314082730, 360582883314464828, 360582882855417586, 360582882396326434, 360582881964047710, 360582883043227194, 360582884122432028]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360548300176635315, 360548306039385396⟩, ⟨1077293387041572044, 1077416965699375150⟩, true⟩

def words06 : List Nat := [360582884417586180, 360582884418000492, 360582883686076548, 360582883113560120, 360582882540963429, 360582881400520480, 360582879233215830, 360582876540887011, 360582873848651848, 360582871870816239]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360542800888253312, 360542806754913137⟩, ⟨1248647683292546155, 1248771383836342095⟩, true⟩

def words07 : List Nat := [360582870762247422, 360582869356903622, 360582867951604842, 360582866035079546, 360582864474695638, 360582862331008346, 360582860187333184, 360582859068411898, 360582858436187758, 360582857152085567]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360620920452653262, 360620926323224016⟩, ⟨(-1187440827858055554), (-1187317005352380288)⟩, true⟩

def words08 : List Nat := [360582855867972148, 360582855868355787, 360582857152902457, 360582858437446014, 360582858652645330, 360582858653060261, 360582858277772277, 360582858207240604, 360582859089535839, 360582860310420567]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598772725115632, 360598778599641704⟩, ⟨(-496471249320935050), (-496347303429096856)⟩, true⟩

def words09 : List Nat := [360582860866651530, 360582861422899014, 360582863002799944, 360582865095664404, 360582866562362819, 360582868029036669, 360582868984566870, 360582869521501106, 360582870031748735, 360582870542097744]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk311B
