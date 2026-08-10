import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk289A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360530724105491967, 360530729112750158⟩, ⟨1506595964135887982, 1506693834906385338⟩, true⟩

def state01 : KState := ⟨⟨360615592516411257, 360615597527276891⟩, ⟨(-946640937128536360), (-946542962085271246)⟩, true⟩

def words00 : List Nat := [360582862043923292, 360582861435204207, 360582861426323360, 360582861386977342, 360582861347604554, 360582860198568441, 360582858310752591, 360582857310766946, 360582856504319047, 360582857637197501]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360581323493365746, 360581328507868473⟩, ⟨44308292741050237, 44406372950490097⟩, true⟩

def words01 : List Nat := [360582857987198446, 360582858337218123, 360582859311686489, 360582861032025412, 360582862447415992, 360582863862770901, 360582864208004098, 360582864208387001, 360582864050603776, 360582863997942833]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598722724971843, 360598727743071872⟩, ⟨(-459104764124036825), (-459006579862303873)⟩, true⟩

def words02 : List Nat := [360582865084934597, 360582865085316717, 360582865037680616, 360582864307283894, 360582863576870836, 360582862111994856, 360582861574142576, 360582861901707184, 360582861902047745, 360582862180876915]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360679211407075672, 360679216428787613⟩, ⟨(-2788170363378958897), (-2788072074606910133)⟩, true⟩

def words03 : List Nat := [360582862699647304, 360582863218488192, 360582864929147249, 360582867021518341, 360582868103938745, 360582869186310988, 360582870779479936, 360582873359054385, 360582876688426327, 360582880017654380]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360664117843121991, 360664122868471805⟩, ⟨(-2351625472434653346), (-2351527078364362512)⟩, true⟩

def words04 : List Nat := [360582882436107525, 360582884241194068, 360582886924831898, 360582889608400337, 360582891460545146, 360582892665098826, 360582893273431641, 360582893881764172, 360582895680527266, 360582898486641666]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk289A
