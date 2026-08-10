import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk616A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk616B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk616A

def state06 : KState := ⟨⟨360598052630996657, 360598076888465073⟩, ⟨(-957316329265987138), (-956305902802277512)⟩, true⟩

def words05 : List Nat := [360582562757392337, 360582563715536112, 360582564541514095, 360582565227049520, 360582565678060445, 360582566129295819, 360582566843163083, 360582567295278524, 360582567547596168, 360582567800016909]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 61650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 61600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360639707935644870, 360639732201280905⟩, ⟨(-3526054500214028111), (-3525043570094294297)⟩, true⟩

def words06 : List Nat := [360582568269525001, 360582568901640705, 360582569445363629, 360582569989222091, 360582570310551864, 360582570590687441, 360582571133486345, 360582571676531087, 360582572421383904, 360582573349144662]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 61660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 61600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360630329152278835, 360630353426146137⟩, ⟨(-2947574210790678828), (-2946562773007949426)⟩, true⟩

def words07 : List Nat := [360582574117109117, 360582574885147210, 360582575915789737, 360582577112873789, 360582578243534601, 360582579374301453, 360582580257986128, 360582580879947688, 360582581655169553, 360582582430653069]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 61670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 61600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360636224397182247, 360636248679190785⟩, ⟨(-3311270745354514418), (-3310258805379572062)⟩, true⟩

def words08 : List Nat := [360582583468555550, 360582584244844104, 360582584859242604, 360582585473730129, 360582585928698231, 360582586560020178, 360582587453752433, 360582588347627305, 360582589109395866, 360582589980103729]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 61680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 61600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360628977124195002, 360629001414380603⟩, ⟨(-2864222692237224367), (-2863210247780408291)⟩, true⟩

def words09 : List Nat := [360582590840870067, 360582591701850239, 360582592525302393, 360582593140711737, 360582593533214897, 360582593925764739, 360582594513800688, 360582595308178983, 360582596061007976, 360582596814004914]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 61690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 61600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 61600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk616B
