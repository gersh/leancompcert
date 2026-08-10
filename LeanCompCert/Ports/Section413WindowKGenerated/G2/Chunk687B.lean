import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk687A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk687B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk687A

def state06 : KState := ⟨⟨360574204511441982, 360574234940239070⟩, ⟨587547567541582412, 588960854807967690⟩, true⟩

def words05 : List Nat := [360582801190703857, 360582800958825573, 360582800726767954, 360582800770455098, 360582800819822962, 360582800869347900, 360582800870219048, 360582800759324792, 360582800521149817, 360582800397697011]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360559011190279531, 360559041628248131⟩, ⟨1632150050136115806, 1633563968081649010⟩, true⟩

def words06 : List Nat := [360582800273935860, 360582799987179570, 360582799489084116, 360582798885440420, 360582798281658040, 360582797551259053, 360582796943556754, 360582796547133810, 360582796150608442, 360582795648432538]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592879510982514, 360592909958125688⟩, ⟨(-697173908202014667), (-695759359275597829)⟩, true⟩

def words07 : List Nat := [360582795303811448, 360582795170532965, 360582795056401911, 360582795057374597, 360582794920576676, 360582794580587753, 360582794240422547, 360582794111565870, 360582794235114979, 360582794383195467]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360569260493598830, 360569290950014789⟩, ⟨927404168896544801, 928819355650994907⟩, true⟩

def words08 : List Nat := [360582794400124403, 360582794503516806, 360582794504312864, 360582794498031723, 360582794491493248, 360582794432024010, 360582794215061659, 360582793892163017, 360582793569101080, 360582793193882372]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565027487324011, 360565057952909250⟩, ⟨1218705397845494491, 1220121215398078613⟩, true⟩

def words09 : List Nat := [360582793013038438, 360582793028659527, 360582793029527570, 360582792909061005, 360582792835701395, 360582792709580370, 360582792616107781, 360582792617081155, 360582792529661735, 360582792272900502]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk687B
