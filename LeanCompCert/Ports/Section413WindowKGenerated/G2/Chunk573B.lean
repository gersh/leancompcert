import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk573A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk573B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk573A

def state06 : KState := ⟨⟨360579768566152464, 360579789437876958⟩, ⟨122293465547142864, 123102312728486342⟩, true⟩

def words05 : List Nat := [360581938256552953, 360581937659760987, 360581937062836582, 360581936700053003, 360581936576238616, 360581936374961793, 360581936173607565, 360581935821431872, 360581935609539883, 360581935573036102]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 57350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 57300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583814945708377, 360583835824961553⟩, ⟨(-109828972856827850), (-109019693791885526)⟩, true⟩

def words06 : List Nat := [360581935631922537, 360581935770124071, 360581935770836612, 360581935755689294, 360581935740428249, 360581935431845072, 360581935426634874, 360581935576437723, 360581935577153789, 360581935567099709]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 57360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 57300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360603672051950739, 360603692938764938⟩, ⟨(-1249117807858037875), (-1248308094980906437)⟩, true⟩

def words07 : List Nat := [360581935826008338, 360581936085157840, 360581936647859737, 360581936907680813, 360581936908428959, 360581936875604730, 360581937058238675, 360581937450165038, 360581937829970905, 360581938209935171]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 57370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 57300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360614195753694103, 360614216648125536⟩, ⟨(-1853152852395331152), (-1852342702402721630)⟩, true⟩

def words08 : List Nat := [360581938420482273, 360581938544465479, 360581938972000540, 360581939399763620, 360581939666156487, 360581939939917276, 360581939940635623, 360581939941307322, 360581940245358861, 360581940808666340]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 57380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 57300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586566107954112, 360586587009935183⟩, ⟨(-267339942033577353), (-266529358729880365)⟩, true⟩

def words09 : List Nat := [360581941532734942, 360581942256933249, 360581942743569257, 360581942927441527, 360581942944343586, 360581942961454019, 360581943281914765, 360581943558860918, 360581943640472036, 360581943722209710]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 57390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 57300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 57300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk573B
