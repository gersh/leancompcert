import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk845A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk845B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk845A

def state06 : KState := ⟨⟨360610976203582920, 360611022978108727⟩, ⟨(-2419005136775469538), (-2416334029036815904)⟩, true⟩

def words05 : List Nat := [360582445979896886, 360582446307041051, 360582446602310582, 360582446800314762, 360582446879546383, 360582446958859969, 360582447059613725, 360582447259141005, 360582447598056835, 360582447937262039]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 84550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 84500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589047357486940, 360589094143573913⟩, ⟨(-564679543366575619), (-562007457958205525)⟩, true⟩

def words06 : List Nat := [360582448193684904, 360582448310577203, 360582448533568654, 360582448756926513, 360582448903404217, 360582448910421489, 360582448911522374, 360582448811475250, 360582448711190778, 360582448751442353]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 84560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 84500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360578849251083987, 360578896048605126⟩, ⟨297863676603812223, 300536729058137925⟩, true⟩

def words07 : List Nat := [360582448896782353, 360582449042350244, 360582449117702052, 360582449198980651, 360582449200001080, 360582449199360345, 360582449304659637, 360582449371895327, 360582449372984839, 360582449332230784]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 84570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 84500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598012956183567, 360598059765183355⟩, ⟨(-1323166387464212745), (-1320492364090595035)⟩, true⟩

def words08 : List Nat := [360582449291219760, 360582449232999326, 360582449333714317, 360582449434659418, 360582449435779748, 360582449417492699, 360582449259384593, 360582449214260779, 360582449261918370, 360582449447725345]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 84580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 84500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585072418673343, 360585119239243852⟩, ⟨(-228452154826838604), (-225777152629589088)⟩, true⟩

def words09 : List Nat := [360582449543444606, 360582449639281011, 360582449811645551, 360582450074445350, 360582450242090983, 360582450409913106, 360582450496996434, 360582450498211326, 360582450477173483, 360582450510119734]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 84590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 84500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 84500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk845B
