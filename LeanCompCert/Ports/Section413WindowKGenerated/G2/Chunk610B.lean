import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk610A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk610B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk610A

def state06 : KState := ⟨⟨360588155540562758, 360588179309814695⟩, ⟨(-349373224460892127), (-348392755194722903)⟩, true⟩

def words05 : List Nat := [360582471318822813, 360582471733125426, 360582471992069197, 360582472288841878, 360582472516796453, 360582472744979321, 360582473241137175, 360582473470286062, 360582473564494125, 360582473658823151]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 61050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 61000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360604464526590003, 360604488303927063⟩, ⟨(-1345390590612777968), (-1344409627630195448)⟩, true⟩

def words06 : List Nat := [360582473659534725, 360582473537688544, 360582473751466400, 360582473965403579, 360582473966200726, 360582473916665452, 360582473782559384, 360582473815784169, 360582474063191120, 360582474424546831]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 61060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 61000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596482133396685, 360596505918875017⟩, ⟨(-857845130601042863), (-856863670391204051)⟩, true⟩

def words07 : List Nat := [360582474651014918, 360582474877574967, 360582475316542050, 360582475942942869, 360582476376299832, 360582476809769065, 360582477108438298, 360582477140207755, 360582477370578022, 360582477601224828]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 61070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 61000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584669458823819, 360584693252369543⟩, ⟨(-136267986532392919), (-135286033525525007)⟩, true⟩

def words08 : List Nat := [360582477921771503, 360582478248939509, 360582478371240837, 360582478493619481, 360582478494336837, 360582478620952220, 360582478720333109, 360582478819872453, 360582478820647788, 360582478752139959]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 61080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 61000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360639081418957608, 360639105220579876⟩, ⟨(-3460603380186723918), (-3459620933743626478)⟩, true⟩

def words09 : List Nat := [360582479056975621, 360582479362061278, 360582479888676848, 360582480374054094, 360582480632820655, 360582480891660541, 360582481358517167, 360582482018392073, 360582482945813800, 360582483873404812]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 61090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 61000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 61000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk610B
