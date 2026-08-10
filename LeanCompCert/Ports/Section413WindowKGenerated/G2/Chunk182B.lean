import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk182A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk182B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk182A

def state06 : KState := ⟨⟨360724212320170254, 360724214239662220⟩, ⟨(-2552633515097600116), (-2552609790892963546)⟩, true⟩

def words05 : List Nat := [360584381053948155, 360584385650631099, 360584393241352736, 360584397854789786, 360584399903003244, 360584401951014537, 360584406992588771, 360584414152102185, 360584421808374547, 360584429463861719]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 18250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 18200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360667042891050939, 360667044812759978⟩, ⟨(-1508991135347691884), (-1508967370648375270)⟩, true⟩

def words06 : List Nat := [360584435597933736, 360584440466099937, 360584445226282674, 360584449986008621, 360584453111232989, 360584453263072793, 360584453263279984, 360584451905934180, 360584452181363519, 360584456702057314]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 18260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 18200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360538037512490310, 360538039436388744⟩, ⟨848543012153959525, 848566816864490229⟩, true⟩

def words07 : List Nat := [360584461368307716, 360584466034090461, 360584469191896315, 360584469378249537, 360584469378445138, 360584467490516561, 360584465602730194, 360584463531905095, 360584462479906749, 360584459940593585]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 18270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 18200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360713201815479911, 360713203741573741⟩, ⟨(-2354439208384912548), (-2354415363531754582)⟩, true⟩

def words08 : List Nat := [360584457401505955, 360584458716413398, 360584462444542894, 360584466172312853, 360584467092870243, 360584467093103164, 360584468974392483, 360584471406624099, 360584476821511357, 360584483859471519]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 18280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 18200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360682528764351688, 360682530692666497⟩, ⟨(-1793474626494340064), (-1793450741008467516)⟩, true⟩

def words09 : List Nat := [360584488264699985, 360584492669468438, 360584497515605947, 360584503861131627, 360584509441910926, 360584515022118123, 360584518745432127, 360584522563844033, 360584527919668255, 360584533274983941]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 18290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 18200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 18200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk182B
