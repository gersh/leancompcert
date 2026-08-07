import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk685

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572237741269520, 360572267931256878⟩, ⟨722907065095996435, 724303962840568009⟩, true⟩

def state01 : KState := ⟨⟨360608229855367860, 360608260054510983⟩, ⟨(-1742693543989969939), (-1741296019031280607)⟩, true⟩

def words00 : List Nat := [360582841616536579, 360582841845351894, 360582842225620711, 360582842606063793, 360582842805191650, 360582842806160045, 360582842990539270, 360582843189765383, 360582843384123101, 360582843756120487]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591527764857462, 360591557973214684⟩, ⟨(-598302224457204764), (-596904068194164578)⟩, true⟩

def words01 : List Nat := [360582843989990068, 360582844223958225, 360582844625778340, 360582845160369467, 360582845608391475, 360582846056575176, 360582846364428325, 360582846459650526, 360582846587577113, 360582846715816308]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360588042713796502, 360588072931292677⟩, ⟨(-359540703352344333), (-358141920844527775)⟩, true⟩

def words02 : List Nat := [360582847056340505, 360582847184334337, 360582847185216489, 360582847136776011, 360582847088179385, 360582847003256956, 360582847004042994, 360582847000693681, 360582846997239002, 360582846947127197]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603581584343846, 360603611810972316⟩, ⟨(-1424521000697638783), (-1423121592306796093)⟩, true⟩

def words03 : List Nat := [360582847236727487, 360582847526603605, 360582847909639673, 360582848080212777, 360582848081114583, 360582848069841179, 360582848058391570, 360582848133141630, 360582848436867414, 360582848740805456]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587616617583797, 360587646853440877⟩, ⟨(-330296738639472283), (-328896697673957577)⟩, true⟩

def words04 : List Nat := [360582848871288028, 360582848872257452, 360582849081802895, 360582849293518877, 360582849451260070, 360582849452229166, 360582849397465963, 360582849225479438, 360582849053316059, 360582849013910105]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk685
