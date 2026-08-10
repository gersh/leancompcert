import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk312A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk312B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk312A

def state06 : KState := ⟨⟨360590056311164306, 360590062209257031⟩, ⟨(-225966126923410033), (-225841445044368619)⟩, true⟩

def words05 : List Nat := [360582832993594644, 360582833177138874, 360582834380922624, 360582836102368871, 360582837010686752, 360582837919007502, 360582838151437120, 360582838151852721, 360582837594418648, 360582837825998519]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360627764261482564, 360627770163495966⟩, ⟨(-1404867390264443992), (-1404742585805790140)⟩, true⟩

def words06 : List Nat := [360582838691837983, 360582840279213350, 360582841141674761, 360582842004125375, 360582842156155611, 360582842839039918, 360582844541242341, 360582846243415335, 360582847151047532, 360582848588048882]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360694932639784331, 360694938545722460⟩, ⟨(-3505633772241445910), (-3505508845037300252)⟩, true⟩

def words07 : List Nat := [360582851044199813, 360582853500315267, 360582856113601792, 360582858308088203, 360582859626464352, 360582860944791838, 360582863281898388, 360582866264988459, 360582869848198475, 360582873431274799]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360633878125210535, 360633884035112106⟩, ⟨(-1595906957544612286), (-1595781906344417272)⟩, true⟩

def words08 : List Nat := [360582876504240064, 360582878557485637, 360582880260070627, 360582881962669792, 360582883406596854, 360582883831060901, 360582883831431506, 360582883746438703, 360582884293295889, 360582885923631348]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360492178128328244, 360492184042146007⟩, ⟨2838689953515238052, 2838815127273140154⟩, true⟩

def words09 : List Nat := [360582887410299526, 360582888896950381, 360582889697859530, 360582889698275623, 360582889480131843, 360582888573515067, 360582887666841255, 360582886297021407, 360582883908396660, 360582881011068472]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk312B
