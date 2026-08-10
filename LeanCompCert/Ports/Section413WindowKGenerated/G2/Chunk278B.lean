import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk278A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk278B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk278A

def state06 : KState := ⟨⟨360607487828610163, 360607492467366036⟩, ⟨(-696301941530072960), (-696214530110556870)⟩, true⟩

def words05 : List Nat := [360582501902498722, 360582502931934179, 360582503501393164, 360582503539938292, 360582503540279718, 360582502483118224, 360582501425962582, 360582501816259278, 360582502713565892, 360582503610896041]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360500729798150412, 360500734440399708⟩, ⟨2278182201325788499, 2278269710089474593⟩, true⟩

def words06 : List Nat := [360582503650181717, 360582503650548854, 360582502405948286, 360582500658598278, 360582498911272533, 360582496836938175, 360582493479046017, 360582489133726133, 360582484788648454, 360582480752207727]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360491480561904266, 360491485207612962⟩, ⟨2536159529672378786, 2536247134866580054⟩, true⟩

def words07 : List Nat := [360582477819480959, 360582475712681019, 360582473605994175, 360582470661879692, 360582468400934127, 360582465714359022, 360582463027868826, 360582461214848601, 360582458597054400, 360582455334401577]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360550292312113767, 360550296961293756⟩, ⟨896113783358258790, 896201485349230374⟩, true⟩

def words08 : List Nat := [360582452071903954, 360582448730858816, 360582446039979032, 360582444631799552, 360582443223696178, 360582440569942204, 360582437065828741, 360582434470426681, 360582431875096473, 360582430395691362]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360561815479963902, 360561820132646534⟩, ⟨574648654948458814, 574736454645119218⟩, true⟩

def words09 : List Nat := [360582429243914350, 360582427446542963, 360582425649229506, 360582425265963396, 360582425266276245, 360582424505925779, 360582423745588218, 360582422061007768, 360582420743522705, 360582420005572883]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk278B
