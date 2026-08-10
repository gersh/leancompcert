import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk484A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk484B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk484A

def state06 : KState := ⟨⟨360507269847584325, 360507284542291668⟩, ⟨3631394766078802993, 3631875957601054091⟩, true⟩

def words05 : List Nat := [360582239302991818, 360582238677001479, 360582238050964517, 360582237181870949, 360582236328258677, 360582235193352716, 360582234058291464, 360582233211935742, 360582231939558317, 360582230393666020]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360536784809932810, 360536799510947046⟩, ⟨2200891200099426922, 2201372697283944256⟩, true⟩

def words06 : List Nat := [360582228847696875, 360582227102797774, 360582225617171166, 360582224556062044, 360582223494947661, 360582222064661379, 360582220575418344, 360582219232373761, 360582217889177546, 360582216731852430]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360524923282617888, 360524937989979589⟩, ⟨2775895568667749083, 2776377373545964907⟩, true⟩

def words07 : List Nat := [360582215795448867, 360582214615104021, 360582213434679907, 360582212678654337, 360582212136325404, 360582211300527558, 360582210464698093, 360582209285585783, 360582207680704672, 360582206500159993]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360557097933504248, 360557112647160591⟩, ⟨1215925781917476462, 1216407891991378396⟩, true⟩

def words08 : List Nat := [360582205319442708, 360582204562944956, 360582203821778277, 360582202864651190, 360582201907451423, 360582200844336140, 360582199996316075, 360582199572394786, 360582199148421790, 360582198394572251]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590237632477830, 360590252352429016⟩, ⟨(-391185811237412294), (-390703395895414856)⟩, true⟩

def words09 : List Nat := [360582197877783931, 360582197785108660, 360582197904739923, 360582197905407437, 360582197693106113, 360582197102263935, 360582196511306730, 360582196444971067, 360582196611615587, 360582196778401771]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk484B
