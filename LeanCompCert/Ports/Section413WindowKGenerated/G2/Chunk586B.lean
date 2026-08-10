import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk586A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk586B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk586A

def state06 : KState := ⟨⟨360585737190645884, 360585759058429474⟩, ⟨(-219490479581361131), (-218623848467436017)⟩, true⟩

def words05 : List Nat := [360582029652663627, 360582030389112621, 360582030893037050, 360582031107070647, 360582031246572855, 360582031386291945, 360582031816426761, 360582032026910443, 360582032091176319, 360582032155572935]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581024082642906, 360581045958153076⟩, ⟨57099891669008914, 57966976064114504⟩, true⟩

def words06 : List Nat := [360582032510395176, 360582033013065302, 360582033558551799, 360582034104172215, 360582034403499309, 360582034413056743, 360582034413733034, 360582034239267210, 360582034064570166, 360582033975471367]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360580593729353962, 360580615612671715⟩, ⟨82336581305001316, 83204123808822120⟩, true⟩

def words07 : List Nat := [360582033959369214, 360582033749236468, 360582033538953119, 360582033659326219, 360582033781123924, 360582033903050476, 360582033903780349, 360582033879689631, 360582033565746358, 360582033542525308]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360578342142953247, 360578364033996281⟩, ⟨214413834582297216, 215281830444718934⟩, true⟩

def words08 : List Nat := [360582033519036023, 360582033426537559, 360582033382610858, 360582033176082916, 360582032969430720, 360582032544802707, 360582032274886164, 360582032285623489, 360582032286360294, 360582032151741123]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360608742196541017, 360608764095321206⟩, ⟨(-1569990127211722541), (-1569121677218249097)⟩, true⟩

def words09 : List Nat := [360582032154249378, 360582032219493574, 360582032574813149, 360582032640733205, 360582032641505994, 360582032445504654, 360582032268324420, 360582032434373107, 360582032890430428, 360582033346659033]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk586B
