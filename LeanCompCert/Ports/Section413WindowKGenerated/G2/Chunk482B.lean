import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk482A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk482B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk482A

def state06 : KState := ⟨⟨360550304042446466, 360550318611205367⟩, ⟨1551083272289728710, 1551558372944524186⟩, true⟩

def words05 : List Nat := [360582478374851575, 360582477283252831, 360582476191504754, 360582475420336968, 360582474454498117, 360582473119820867, 360582471785071857, 360582470357454844, 360582469263719848, 360582468598212092]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360501490490452340, 360501505065530655⟩, ⟨3906959118561741339, 3907434524223244689⟩, true⟩

def words06 : List Nat := [360582467932634548, 360582467053446238, 360582465901290851, 360582464851536253, 360582463801659036, 360582462456733326, 360582460682563558, 360582458666050318, 360582456649491719, 360582454610262854]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360461713350394376, 360461727931736723⟩, ⟨5827342420560628789, 5827818128617583225⟩, true⟩

def words07 : List Nat := [360582452933819011, 360582451685420975, 360582450436990511, 360582448975146108, 360582447084105852, 360582445079947015, 360582443075669696, 360582441271569161, 360582439174623385, 360582436675080087]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360533735059640027, 360533749647250481⟩, ⟨2349768985363495877, 2350244996075662989⟩, true⟩

def words08 : List Nat := [360582434175487885, 360582432103845249, 360582430302482910, 360582428793685894, 360582427284905901, 360582425361933060, 360582423454613794, 360582421891678592, 360582420328613505, 360582419040418335]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360530158703386227, 360530173297332291⟩, ⟨2522397309322282263, 2522873626010942459⟩, true⟩

def words09 : List Nat := [360582418033174459, 360582416812726428, 360582415592210879, 360582414362174257, 360582413348793413, 360582412098552353, 360582410848291934, 360582409294701495, 360582407786424953, 360582406705738315]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk482B
