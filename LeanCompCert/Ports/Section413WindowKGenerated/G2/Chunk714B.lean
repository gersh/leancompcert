import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk714A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk714B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk714A

def state06 : KState := ⟨⟨360611606096553442, 360611639062758496⟩, ⟨(-2097154658881209321), (-2095563450292335419)⟩, true⟩

def words05 : List Nat := [360582309878432647, 360582310283609322, 360582310884123266, 360582311583532133, 360582312201608800, 360582312819858170, 360582313340130430, 360582313665084728, 360582314076281083, 360582314487811430]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589283700845100, 360589316676610536⟩, ⟨(-501983939219310749), (-500392047397907121)⟩, true⟩

def words06 : List Nat := [360582314869643610, 360582315056251155, 360582315077026289, 360582315097895030, 360582315098743647, 360582315156500693, 360582315220014371, 360582315283717336, 360582315284630102, 360582315346736911]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360626066675074756, 360626099660407279⟩, ⟨(-3131057317648753058), (-3129464742020244278)⟩, true⟩

def words07 : List Nat := [360582315640962149, 360582315935476524, 360582316425126225, 360582316857171951, 360582317120748607, 360582317384395547, 360582317643714845, 360582318061956787, 360582318675278018, 360582319288811747]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360604421142679972, 360604454137668238⟩, ⟨(-1583778985117785345), (-1582185719250579849)⟩, true⟩

def words08 : List Nat := [360582319804445598, 360582320179512875, 360582320749763855, 360582321320317909, 360582321749057328, 360582322061496733, 360582322243270379, 360582322425136264, 360582322569589746, 360582322880317655]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571551834858490, 360571584839411849⟩, ⟨766206812463419202, 767800762186323600⟩, true⟩

def words09 : List Nat := [360582323182261193, 360582323484376013, 360582323688676498, 360582323697851563, 360582323698700526, 360582323634078369, 360582323569151239, 360582323512356278, 360582323460737640, 360582323311610260]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk714B
