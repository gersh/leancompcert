import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk943A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk943B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk943A

def state06 : KState := ⟨⟨362490691693063366, 362490826917801202⟩, ⟨(-542540866318156344), (-533925877153185058)⟩, true⟩

def words05 : List Nat := [371285167812496807, 371285167949025641, 371285168062601036, 371285168097684718, 371285168162497733, 371285168228945958, 371285168393887368, 371285168459470596, 371285168521907177, 371285168585681437]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 94350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 94300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488708521598387, 362488843775895081⟩, ⟨(-355327503554977859), (-346709725063341661)⟩, true⟩

def words06 : List Nat := [371285168749147702, 371285168858010650, 371285169073186475, 371285169289676815, 371285169485143355, 371285169559800137, 371285169638891092, 371285169719687239, 371285169832396169, 371285169874748931]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 94360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 94300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491647508850999, 362491782793227075⟩, ⟨(-632685491111111042), (-624064873882243120)⟩, true⟩

def words07 : List Nat := [371285169914745693, 371285169955828753, 371285170077860206, 371285170162283242, 371285170274647814, 371285170388304989, 371285170498161016, 371285170501466558, 371285170531504495, 371285170605669387]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 94370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 94300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481263103651688, 362481398417469635⟩, ⟨347440516578445098, 356063912686243090⟩, true⟩

def words08 : List Nat := [371285170708957814, 371285170712264897, 371285170685170767, 371285170659594266, 371285170632698695, 371285170634810896, 371285170609547290, 371285170643150531, 371285170677133085, 371285170680555622]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 94380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 94300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492946288554657, 362493081632291846⟩, ⟨(-755425158869361681), (-746798938540420827)⟩, true⟩

def words09 : List Nat := [371285170659878214, 371285170680950020, 371285170755864674, 371285170759170955, 371285170698063347, 371285170616773365, 371285170561617306, 371285170565261154, 371285170622817927, 371285170710389108]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 94390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 94300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 94300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk943B
