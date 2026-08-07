import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk129

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360556214279036230, 360556215206721266⟩, ⟨313855713788703964, 313863819817500406⟩, true⟩

def state01 : KState := ⟨⟨360417884006875113, 360417884936061065⟩, ⟨2098394719942712512, 2098402845340864670⟩, true⟩

def words00 : List Nat := [360580543849579227, 360580539257066658, 360580528698455368, 360580512404827121, 360580496113698374, 360580476700518254, 360580460482242752, 360580450240183831, 360580439999692437, 360580425822609545]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 12900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 12900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360641171549314826, 360641172480003099⟩, ⟨(-785562789070956468), (-785554644270390514)⟩, true⟩

def words01 : List Nat := [360580413233404923, 360580406617741118, 360580400003055909, 360580396507274497, 360580392354052684, 360580382108857777, 360580371865218970, 360580367589237940, 360580371036782644, 360580375742577947]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 12910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 12900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360639797498269069, 360639798430476757⟩, ⟨(-767926880071903446), (-767918715632973502)⟩, true⟩

def words02 : List Nat := [360580376672391029, 360580380643811054, 360580390577597950, 360580400509895532, 360580406101461957, 360580409187914602, 360580409188056799, 360580408852857816, 360580408517682590, 360580412558105481]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 12920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 12900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360472069507063307, 360472070440773642⟩, ⟨1402103503457214903, 1402111687332896687⟩, true⟩

def words03 : List Nat := [360580420961865790, 360580429364356884, 360580434783733395, 360580437592292339, 360580437592426566, 360580437144824618, 360580438143237613, 360580438143397189, 360580433659352909, 360580425285235226]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 12930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 12900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360527479936666136, 360527480871885476⟩, ⟨684834869473597113, 684843072883203179⟩, true⟩

def words04 : List Nat := [360580416912376021, 360580415114462803, 360580415114594334, 360580414407468932, 360580413700440323, 360580407912403683, 360580396200754954, 360580384791448457, 360580373383857240, 360580364506857152]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 12940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 12900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360645892898105722, 360645893834846943⟩, ⟨(-849429144007885449), (-849420920882356377)⟩, true⟩

def words05 : List Nat := [360580360423637754, 360580353261884141, 360580346101206037, 360580347964043022, 360580349485876848, 360580351007501804, 360580351007646620, 360580347913373600, 360580352096940906, 360580357153967200]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 12950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 12900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595452051974779, 360595452990220896⟩, ⟨(-195765491589809458), (-195757248953016218)⟩, true⟩

def words06 : List Nat := [360580363833480848, 360580364597454247, 360580364597596894, 360580361442597522, 360580358288056251, 360580353576160843, 360580356090953811, 360580360310086193, 360580360310231003, 360580361073718467]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 12960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 12900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360721127067644244, 360721128007403800⟩, ⟨(-1826963534090576565), (-1826955271817169079)⟩, true⟩

def words07 : List Nat := [360580361073850587, 360580359506099238, 360580362291606392, 360580365073084309, 360580365073231978, 360580362769448811, 360580360670353792, 360580365600772884, 360580376445463904, 360580387288521036]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 12970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 12900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360635645548746883, 360635646490029069⟩, ⟨(-717560113263259781), (-717551831218522053)⟩, true⟩

def words08 : List Nat := [360580395152708055, 360580397122130507, 360580405002886396, 360580412882474931, 360580416352884948, 360580416708238557, 360580416708383409, 360580412619796564, 360580408531808561, 360580411956027182]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 12980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 12900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360452044177288302, 360452045120082208⟩, ⟨1668509983672524579, 1668518285362006587⟩, true⟩

def words09 : List Nat := [360580417008135306, 360580422059498203, 360580423257756435, 360580423257916703, 360580420996410575, 360580415539659675, 360580410083700090, 360580407863261338, 360580402553976684, 360580392680494671]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 12990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 12900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 12900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk129
