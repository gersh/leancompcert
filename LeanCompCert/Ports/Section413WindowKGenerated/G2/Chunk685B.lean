import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk685A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk685B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk685A

def state06 : KState := ⟨⟨360573791055262702, 360573821300253493⟩, ⟨617478928480301766, 618879595607145336⟩, true⟩

def words05 : List Nat := [360582849074065066, 360582849134399074, 360582849135271351, 360582849087671465, 360582848884448757, 360582848627857130, 360582848370987751, 360582848287241613, 360582848262823290, 360582848132161416]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580191179586463, 360580221433724322⟩, ⟨178590326827185763, 179991621122701315⟩, true⟩

def words06 : List Nat := [360582848001286282, 360582847857207308, 360582847846736686, 360582847783084241, 360582847719373624, 360582847457087355, 360582846982184095, 360582846719905458, 360582846457350131, 360582846366218456]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567064840560311, 360567095103955043⟩, ⟨1078770381679040823, 1080172310762476971⟩, true⟩

def words07 : List Nat := [360582846328811601, 360582846161647736, 360582845994285622, 360582846106318569, 360582846119164878, 360582846132164151, 360582846133027904, 360582846039742780, 360582845876555226, 360582845648002324]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575423109026022, 360575453381551367⟩, ⟨505491898065292587, 506894453371545669⟩, true⟩

def words08 : List Nat := [360582845419122839, 360582845402670340, 360582845241817762, 360582844974817574, 360582844707673606, 360582844256872927, 360582843990818476, 360582843893031741, 360582843795145504, 360582843590814694]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589924072154272, 360589954353844454⟩, ⟨(-489286889585528254), (-487883705618735222)⟩, true⟩

def words09 : List Nat := [360582843547276883, 360582843611764852, 360582843612562945, 360582843603649393, 360582843382418474, 360582842954952353, 360582842527306403, 360582842312089860, 360582842345450931, 360582842450145985]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk685B
