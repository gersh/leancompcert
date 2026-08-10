import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk870A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk870B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk870A

def state06 : KState := ⟨⟨362482090462203397, 362482204859710786⟩, ⟨253530592213706243, 260255239769015653⟩, true⟩

def words05 : List Nat := [371285194297882578, 371285194243817411, 371285194250289288, 371285194269398949, 371285194303034539, 371285194337867074, 371285194352067616, 371285194355107075, 371285194268226086, 371285194237608432]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472719534999639, 362472833959473018⟩, ⟨1069406286272421287, 1076133281630076595⟩, true⟩

def words06 : List Nat := [371285194231825971, 371285194234856288, 371285194100120523, 371285193966557881, 371285193831824750, 371285193704300969, 371285193528272688, 371285193473575587, 371285193417883545, 371285193363189914]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491053078836093, 362491167530791349⟩, ⟨(-526977605279842885), (-520248216940085101)⟩, true⟩

def words07 : List Nat := [371285193223298564, 371285193216800330, 371285193253428624, 371285193256481966, 371285193210818714, 371285193145855039, 371285193108525006, 371285193111869632, 371285193156410482, 371285193228510254]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479019192535611, 362479133671807748⟩, ⟨520964270236513328, 527696037471453360⟩, true⟩

def words08 : List Nat := [371285193299520513, 371285193302551252, 371285193222414598, 371285193250814574, 371285193318054415, 371285193321085218, 371285193212839882, 371285193061025533, 371285192907941167, 371285192875361216]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480473585299576, 362480588091831809⟩, ⟨394309232806551819, 401043374262422457⟩, true⟩

def words09 : List Nat := [371285192807849953, 371285192806043537, 371285192803262042, 371285192801321617, 371285192688988448, 371285192618547912, 371285192590531875, 371285192593585747, 371285192542839145, 371285192493373284]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk870B
