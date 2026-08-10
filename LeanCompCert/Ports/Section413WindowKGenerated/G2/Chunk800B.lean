import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk800A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk800B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk800A

def state06 : KState := ⟨⟨360594476976723269, 360594518727625670⟩, ⟨(-990796919439664628), (-988539416344895316)⟩, true⟩

def words05 : List Nat := [360582170853917796, 360582170907862290, 360582171005835908, 360582171058408091, 360582171059474984, 360582170975506640, 360582170929735442, 360582171089176176, 360582171244347755, 360582171399758858]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581018128237756, 360581059890046176⟩, ⟨86687829408799070, 88946205692139560⟩, true⟩

def words06 : List Nat := [360582171476950356, 360582171478095279, 360582171399505636, 360582171357668676, 360582171315517642, 360582171209166320, 360582171176287146, 360582171044096008, 360582170911695458, 360582170745618702]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560972651242847, 360561014423849274⟩, ⟨1691882319661642392, 1694141560595196156⟩, true⟩

def words07 : List Nat := [360582170874564028, 360582171017598482, 360582171028883997, 360582171030029113, 360582170885581979, 360582170700566439, 360582170515219399, 360582170485842795, 360582170300707154, 360582170037742821]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579133465154650, 360579175248558287⟩, ⟨237500637394825062, 239760743022628690⟩, true⟩

def words08 : List Nat := [360582169774491108, 360582169629243739, 360582169604408607, 360582169646701445, 360582169647760122, 360582169564392831, 360582169408146720, 360582169187122536, 360582168965767150, 360582168889999449]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571570782853551, 360571612577173063⟩, ⟨843193629587168216, 845454609520948944⟩, true⟩

def words09 : List Nat := [360582168853658609, 360582168697328532, 360582168540787741, 360582168377564303, 360582168334398359, 360582168234597330, 360582168134674066, 360582167956908478, 360582167696509613, 360582167566055972]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk800B
