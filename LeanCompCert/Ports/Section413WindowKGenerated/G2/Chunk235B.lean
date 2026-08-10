import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk235A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk235B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk235A

def state06 : KState := ⟨⟨360591909723510893, 360591912992448838⟩, ⟨(-247782753046706022), (-247730648191841994)⟩, true⟩

def words05 : List Nat := [360581378315242150, 360581383582214440, 360581387933517731, 360581390498823168, 360581391837944772, 360581393177030608, 360581396312466882, 360581397662336533, 360581398108930958, 360581398555532246]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360670146834177531, 360670150106013123⟩, ⟨(-2091052677016835290), (-2091000503879399728)⟩, true⟩

def words06 : List Nat := [360581400798009065, 360581404889937521, 360581410777248642, 360581416664118604, 360581421016885067, 360581423584853456, 360581427948015520, 360581432310896678, 360581435616774553, 360581439380805054]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566115001196850, 360566118275953526⟩, ⟨361643971805887360, 361696213807786294⟩, true⟩

def words07 : List Nat := [360581442073409470, 360581444765816051, 360581447726469926, 360581451583980834, 360581454208247529, 360581456832345915, 360581458325395734, 360581458325702338, 360581458036142594, 360581457385953857]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360604528952718355, 360604532230366846⟩, ⟨(-544426828264888941), (-544374518059136061)⟩, true⟩

def words08 : List Nat := [360581457878881983, 360581458526789489, 360581458527067521, 360581457801956447, 360581457076855121, 360581455524527424, 360581455459976699, 360581456052757582, 360581456053033542, 360581456713514694]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360675433953607320, 360675437234152806⟩, ⟨(-2217528450398880469), (-2217476071839044873)⟩, true⟩

def words09 : List Nat := [360581458744965839, 360581460776334041, 360581464599291210, 360581467321987099, 360581468304473819, 360581469286898821, 360581470210394002, 360581472401524129, 360581476383333250, 360581480364874427]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk235B
