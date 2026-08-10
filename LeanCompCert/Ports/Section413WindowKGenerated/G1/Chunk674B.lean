import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk674A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk674B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk674A

def state06 : KState := ⟨⟨362488932545866755, 362488999889168964⟩, ⟨(-239480909205448500), (-236412620985797228)⟩, true⟩

def words05 : List Nat := [371285495035405079, 371285495055989419, 371285495294835343, 371285495297140016, 371285495298633950, 371285495266409127, 371285495343877057, 371285495347130566, 371285495400671809, 371285495455185095]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476990007833817, 362477057371902379⟩, ⟨566178024814961868, 569247714038538314⟩, true⟩

def words06 : List Nat := [371285495520559641, 371285495522862766, 371285495321739490, 371285495234835452, 371285495146749155, 371285495105692532, 371285494910653618, 371285494708147670, 371285494504735248, 371285494421169291]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472500788246739, 362472568173095113⟩, ⟨869149396479052662, 872220487823795004⟩, true⟩

def words07 : List Nat := [371285494375196821, 371285494455236560, 371285494470228205, 371285494472547443, 371285494290468231, 371285494176159290, 371285494163021372, 371285494165325118, 371285493976807669, 371285493787911708]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478885282612208, 362478952688082805⟩, ⟨438327637634982043, 441400120669905595⟩, true⟩

def words08 : List Nat := [371285493625741574, 371285493628307644, 371285493603459486, 371285493641370477, 371285493643165101, 371285493614425061, 371285493329159341, 371285493119559063, 371285492915661142, 371285492918052726]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486674754722112, 362486742181177277⟩, ⟨(-87397751563070074), (-84323852176826588)⟩, true⟩

def words09 : List Nat := [371285492822885946, 371285492727465220, 371285492752528682, 371285492797690848, 371285492908903547, 371285493021045883, 371285493114439296, 371285493116743843, 371285492936062127, 371285492957429824]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk674B
