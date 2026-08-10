import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk956A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk956B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk956A

def state06 : KState := ⟨⟨360611197643324901, 360611258079305486⟩, ⟨(-2783033117382803972), (-2779129296644466048)⟩, true⟩

def words05 : List Nat := [360582204027236055, 360582204254996690, 360582204546999258, 360582204811252550, 360582204970675760, 360582205130190736, 360582205341154003, 360582205616479163, 360582205921308553, 360582206226443354]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 95650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 95600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360600432263936792, 360600492713152005⟩, ⟨(-1753179200487353449), (-1749274113659832981)⟩, true⟩

def words06 : List Nat := [360582206475829534, 360582206727967176, 360582207070029828, 360582207412492820, 360582207694599609, 360582207911775363, 360582208032495674, 360582208153350666, 360582208253379219, 360582208446094487]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 95660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 95600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587007323444332, 360587067785723415⟩, ⟨(-468739498024688263), (-464833161312049349)⟩, true⟩

def words07 : List Nat := [360582208696834859, 360582208947834997, 360582209143695447, 360582209230763558, 360582209263350562, 360582209296334046, 360582209419547733, 360582209526137760, 360582209578161089, 360582209630381059]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 95670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 95600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360599434344328262, 360599494819711377⟩, ⟨(-1657815636384303562), (-1653908045811872336)⟩, true⟩

def words08 : List Nat := [360582209767955365, 360582209977730774, 360582210184333655, 360582210391181648, 360582210505801722, 360582210511611253, 360582210600907354, 360582210690624909, 360582210796452552, 360582210978537057]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 95680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 95600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588864780211495, 360588925268802669⟩, ⟨(-646379112344925671), (-642470257832092843)⟩, true⟩

def words09 : List Nat := [360582211099148734, 360582211219909864, 360582211320468146, 360582211490109063, 360582211631513831, 360582211773142165, 360582211831582904, 360582211832970614, 360582211889381058, 360582211961127388]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 95690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 95600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 95600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk956B
