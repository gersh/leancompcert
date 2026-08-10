import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk165A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk165B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk165A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk165B
