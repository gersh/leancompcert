import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk845

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575381664266955, 360575428369848747⟩, ⟨589934359243306265, 592599639151838139⟩, true⟩

def state01 : KState := ⟨⟨360592980288012812, 360593027005160525⟩, ⟨(-897317431339926834), (-894651174055493746)⟩, true⟩

def words00 : List Nat := [360582441301428292, 360582441127465328, 360582440993189889, 360582440996895372, 360582440997910897, 360582440966194435, 360582440929655506, 360582440796515547, 360582440668723953, 360582440795388360]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 84500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 84500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360572023721781392, 360572070450368148⟩, ⟨873797482990930265, 876464707047861679⟩, true⟩

def words01 : List Nat := [360582440917912656, 360582441040652150, 360582441049471097, 360582441050684754, 360582440919595150, 360582440753577614, 360582440587207660, 360582440532176134, 360582440480785603, 360582440359348838]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 84510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 84500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360610752231198347, 360610798971241546⟩, ⟨(-2399720144562186032), (-2397051952151637204)⟩, true⟩

def words02 : List Nat := [360582440254830932, 360582440343489172, 360582440571664317, 360582440800078274, 360582440890278921, 360582440940300516, 360582441109258272, 360582441278581005, 360582441558980978, 360582441895705333]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 84520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 84500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592671176399411, 360592717928014983⟩, ⟨(-871181597816579229), (-868512427136156757)⟩, true⟩

def words03 : List Nat := [360582442146686790, 360582442397813539, 360582442788522022, 360582443256872588, 360582443610599610, 360582443964508305, 360582444232757253, 360582444413672062, 360582444536197852, 360582444659102430]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 84530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 84500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598128151035980, 360598174914086884⟩, ⟨(-1332594882510122218), (-1329924745031662702)⟩, true⟩

def words04 : List Nat := [360582444828941815, 360582444917062388, 360582444934966837, 360582444953003318, 360582444954019946, 360582444992988186, 360582445173842459, 360582445354926691, 360582445465811670, 360582445653107929]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 84540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 84500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk845
