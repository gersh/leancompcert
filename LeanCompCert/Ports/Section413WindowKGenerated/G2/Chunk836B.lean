import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk836A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk836B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk836A

def state06 : KState := ⟨⟨360603708797923081, 360603754544143100⟩, ⟨(-1785098879800926638), (-1782514263664799458)⟩, true⟩

def words05 : List Nat := [360582446085025123, 360582446363530468, 360582446784476902, 360582447095001208, 360582447267025147, 360582447439114993, 360582447498366179, 360582447638145958, 360582447893800646, 360582448149721987]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360604460823275238, 360604506580923573⟩, ⟨(-1848109999396318315), (-1845524427110331783)⟩, true⟩

def words06 : List Nat := [360582448324165493, 360582448404330678, 360582448627029675, 360582448850111631, 360582449005817348, 360582449139792635, 360582449196789521, 360582449253921724, 360582449397444657, 360582449662431977]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596420909816564, 360596466678781084⟩, ⟨(-1175372739058307795), (-1172786219890598677)⟩, true⟩

def words07 : List Nat := [360582449923328433, 360582450184431790, 360582450373661300, 360582450586953933, 360582450762807736, 360582450938977410, 360582451137015054, 360582451377291212, 360582451545847503, 360582451714573073]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360609982542626925, 360610028322917051⟩, ⟨(-2310315321196874228), (-2307727854245066186)⟩, true⟩

def words08 : List Nat := [360582451871414727, 360582452100638487, 360582452431526725, 360582452762637046, 360582452957576563, 360582453010101926, 360582453161462901, 360582453313181610, 360582453607201116, 360582453937926490]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589232231511708, 360589278023269833⟩, ⟨(-573548685965570273), (-570960259204500557)⟩, true⟩

def words09 : List Nat := [360582454165776922, 360582454393761499, 360582454735910193, 360582455194589423, 360582455584994795, 360582455975584698, 360582456274408432, 360582456430915113, 360582456513409971, 360582456596295192]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk836B
