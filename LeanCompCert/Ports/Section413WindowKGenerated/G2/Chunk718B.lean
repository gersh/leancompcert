import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk718A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk718B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk718A

def state06 : KState := ⟨⟨360578618314855097, 360578651665908099⟩, ⟨263451225532724812, 265070012385828462⟩, true⟩

def words05 : List Nat := [360582339888625532, 360582340174523500, 360582340341045028, 360582340398450289, 360582340399318713, 360582340322800897, 360582340328105752, 360582340415696550, 360582340416607765, 360582340366330947]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594683067824984, 360594716428516020⟩, ⟨(-890983709706387323), (-889364230217078071)⟩, true⟩

def words06 : List Nat := [360582340457785385, 360582340775016081, 360582341067478279, 360582341360126611, 360582341488211202, 360582341489231156, 360582341551149555, 360582341679452253, 360582341803413788, 360582341976647853]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592408252201451, 360592441622610497⟩, ⟨(-727485908173927624), (-725865730204971544)⟩, true⟩

def words07 : List Nat := [360582342053168230, 360582342129797619, 360582342322405180, 360582342661623367, 360582342900832455, 360582343140219516, 360582343232841123, 360582343233861362, 360582343322473579, 360582343464123485]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600103316683318, 360600136696710083⟩, ⟨(-1280708422541032669), (-1279087553202295809)⟩, true⟩

def words08 : List Nat := [360582343798617142, 360582343983646331, 360582344010877477, 360582344038194223, 360582344039053900, 360582343941219311, 360582344131731424, 360582344324171740, 360582344408063248, 360582344656632712]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360605586723736223, 360605620113391310⟩, ⟨(-1675020684965772330), (-1673399123399055654)⟩, true⟩

def words09 : List Nat := [360582344906324667, 360582345156318288, 360582345472144498, 360582345647959654, 360582345658857550, 360582345669843896, 360582345676615129, 360582345808341708, 360582346132870633, 360582346457622975]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk718B
