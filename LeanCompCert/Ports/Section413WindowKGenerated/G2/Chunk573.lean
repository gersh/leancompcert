import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk573

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579013073535346, 360579033899863154⟩, ⟨166168085078364601, 166974329669733995⟩, true⟩

def state01 : KState := ⟨⟨360593756936302566, 360593777770165686⟩, ⟨(-678700309979374466), (-677893633576383580)⟩, true⟩

def words00 : List Nat := [360581948140537177, 360581948402239746, 360581948512430996, 360581948622705218, 360581948623373949, 360581948746130906, 360581948984609024, 360581949223230168, 360581949229225228, 360581949436450058]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 57300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 57300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607000359233151, 360607021200632527⟩, ⟨(-1437757574247958464), (-1436950465904389074)⟩, true⟩

def words01 : List Nat := [360581949877467307, 360581950318711813, 360581950934487891, 360581951246838830, 360581951301809379, 360581951356855461, 360581951501424881, 360581951842297507, 360581952280302371, 360581952718472335]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 57310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 57300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360571426417412874, 360571447266445184⟩, ⟨601289008993683916, 602096554891693976⟩, true⟩

def words02 : List Nat := [360581952924353604, 360581952925152913, 360581952827453254, 360581952623742004, 360581952419824460, 360581952137499745, 360581951551610386, 360581950786670928, 360581950021605049, 360581949561140661]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 57320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 57300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360531443701227370, 360531464557777964⟩, ⟨2893831349390214303, 2894639326350082909⟩, true⟩

def words03 : List Nat := [360581949499689168, 360581949621578965, 360581949622291749, 360581949560763823, 360581949267295383, 360581948896386760, 360581948525267813, 360581948145641146, 360581947462587554, 360581946583002068]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 57330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 57300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360560944281036187, 360560965145135396⟩, ⟨1202020461508861833, 1202828871342866819⟩, true⟩

def words04 : List Nat := [360581945703267500, 360581944924833558, 360581944331932762, 360581943639865733, 360581942947746678, 360581941998867554, 360581940850271502, 360581940006065254, 360581939161644637, 360581938621531959]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 57340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 57300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk573
