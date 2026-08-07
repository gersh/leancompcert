import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk165

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360628977882019234, 360628979434854278⟩, ⟨(-759576783170578837), (-759559437390803261)⟩, true⟩

def state01 : KState := ⟨⟨360656448420880692, 360656449975673921⟩, ⟨(-1213151571356589102), (-1213134193256785462)⟩, true⟩

def words00 : List Nat := [360582952939043095, 360582955801556040, 360582956811617750, 360582957821579804, 360582957862104804, 360582960794811598, 360582964887819973, 360582968980371739, 360582971223594700, 360582975674101831]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 16500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 16500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360688390358129288, 360688391914888879⟩, ⟨(-1741207832517819819), (-1741190421943401917)⟩, true⟩

def words01 : List Nat := [360582978908910461, 360582982143386491, 360582985084910327, 360582986492169677, 360582986492363266, 360582984729787499, 360582983870896284, 360582986598081124, 360582992978716805, 360582999358630578]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 16510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 16500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360624899940593142, 360624901499336430⟩, ⟨(-692537894624108555), (-692520451269433849)⟩, true⟩

def words02 : List Nat := [360583003893480904, 360583007941374068, 360583011200981541, 360583014460257042, 360583016786673289, 360583016786881647, 360583015485707987, 360583011351635962, 360583007218024471, 360583009269509473]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 16520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 16500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360528399159192571, 360528400719897880⟩, ⟨903457752874440105, 903475228671310241⟩, true⟩

def words03 : List Nat := [360583014162528552, 360583019054995468, 360583021083201877, 360583023250237474, 360583024451582907, 360583025652839052, 360583028475253145, 360583028475461677, 360583027675886950, 360583024373384659]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 16530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 16500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360524347188171704, 360524348750849411⟩, ⟨970461820480425036, 970479328910528546⟩, true⟩

def words04 : List Nat := [360583021071238098, 360583016064967394, 360583012940963131, 360583012199945857, 360583011459000370, 360583007645105808, 360583000212586067, 360582996423047191, 360582992633902916, 360582987985224670]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 16540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 16500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360510934475744865, 360510936040411021⟩, ⟨1192536915442168421, 1192554456790947589⟩, true⟩

def words05 : List Nat := [360582984442470411, 360582979014642743, 360582973587431136, 360582972184749148, 360582972184928176, 360582968977905423, 360582965771247291, 360582960727057735, 360582954547133241, 360582950198429799]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 16550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 16500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360624510593625104, 360624512160261479⟩, ⟨(-688654752297185774), (-688637178311699338)⟩, true⟩

def words06 : List Nat := [360582945850180480, 360582945878402779, 360582945878588931, 360582944783224212, 360582943687957677, 360582942433459631, 360582946867300095, 360582951300645647, 360582952885554532, 360582955393722846]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 16560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 16500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360681872867281394, 360681874435890410⟩, ⟨(-1639467951937883500), (-1639450345255812428)⟩, true⟩

def words07 : List Nat := [360582960293664975, 360582965193076601, 360582973722408811, 360582978643369560, 360582980235411449, 360582981827279752, 360582983598444910, 360582987268289964, 360582993232703334, 360582999196444309]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 16570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 16500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360534563706651755, 360534565277254947⟩, ⟨803014059616921109, 803031699372172815⟩, true⟩

def words08 : List Nat := [360583003330554735, 360583003859409640, 360583003859582033, 360583002937246214, 360583002014966809, 360582999486469039, 360582993354337469, 360582984738143561, 360582976122946148, 360582969840206857]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 16580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 16500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360384937863405615, 360384939435977958⟩, ⟨3286374763483370162, 3286392435916889678⟩, true⟩

def words09 : List Nat := [360582966922856974, 360582966288785411, 360582965654766867, 360582963196956284, 360582957138561115, 360582950124257490, 360582943110739027, 360582935979676715, 360582926810658171, 360582914883924759]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 16590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 16500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 16500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk165
