import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk968A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360629995793652962, 360630057735384015⟩, ⟨(-4622896890189522664), (-4618848169395591044)⟩, true⟩

def state01 : KState := ⟨⟨360616176525466233, 360616238480580145⟩, ⟨(-3285226765999044666), (-3281176749678370718)⟩, true⟩

def words00 : List Nat := [360582343282129028, 360582343651423005, 360582344017898267, 360582344384773187, 360582344701347488, 360582344941318682, 360582345107907620, 360582345274644429, 360582345526262117, 360582345877986655]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 96800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 96800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360572781339619455, 360572843307950521⟩, ⟨916099023409005532, 920150319350032406⟩, true⟩

def words01 : List Nat := [360582346196772302, 360582346515807493, 360582346772051231, 360582346922096345, 360582347000522427, 360582347079316095, 360582347155169809, 360582347156574708, 360582347126193605, 360582347029488944]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 96810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 96800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604612255231978, 360604674236828135⟩, ⟨(-2165906213099471042), (-2161853632768429868)⟩, true⟩

def words02 : List Nat := [360582346941015332, 360582347037267735, 360582347239780733, 360582347442593776, 360582347553983049, 360582347559161329, 360582347670765421, 360582347782779903, 360582347955987342, 360582348188013516]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 96820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 96800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360600877208940116, 360600939203946754⟩, ⟨(-1804272334843665139), (-1800218455910290403)⟩, true⟩

def words03 : List Nat := [360582348328749679, 360582348469604980, 360582348626380678, 360582348836583923, 360582349009735680, 360582349183113637, 360582349286663620, 360582349392790249, 360582349585890171, 360582349779468380]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 96830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 96800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604405093309874, 360604467101546674⟩, ⟨(-2145955807872510634), (-2141900647664436040)⟩, true⟩

def words04 : List Nat := [360582350059645159, 360582350277628262, 360582350431664720, 360582350585859567, 360582350667508370, 360582350802500964, 360582351043727845, 360582351285219162, 360582351450649364, 360582351680460011]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 96840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 96800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk968A
