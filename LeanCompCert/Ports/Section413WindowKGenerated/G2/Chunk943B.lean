import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk943A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk943B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk943A

def state06 : KState := ⟨⟨360596768203727674, 360596826945977399⟩, ⟨(-1394416010504079771), (-1390673113658378965)⟩, true⟩

def words05 : List Nat := [360582087448402893, 360582087706458871, 360582087877908155, 360582088068358879, 360582088219714520, 360582088371443612, 360582088612202526, 360582088835522960, 360582088992930715, 360582089150557063]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360596966026452516, 360597024781594729⟩, ⟨(-1412998717914139665), (-1409254604469207243)⟩, true⟩

def words06 : List Nat := [360582089397593272, 360582089701022317, 360582090100224103, 360582090499680581, 360582090802134219, 360582091043265824, 360582091200769505, 360582091358643512, 360582091489891813, 360582091649547075]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594640037775566, 360594698805936974⟩, ⟨(-1193489069874381544), (-1189743727746903624)⟩, true⟩

def words07 : List Nat := [360582091747134372, 360582091844868815, 360582091991671691, 360582092226661380, 360582092425358806, 360582092624274232, 360582092758765817, 360582092781493906, 360582092916165454, 360582093051306838]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584232725080388, 360584291506114607⟩, ⟨(-211243503319104865), (-207496946189971313)⟩, true⟩

def words08 : List Nat := [360582093157574878, 360582093198144985, 360582093199374189, 360582093184004810, 360582093168409342, 360582093105860644, 360582093155995694, 360582093214521405, 360582093215739419, 360582093235663082]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594081454952484, 360594140248892799⟩, ⟨(-1140997390314332889), (-1137249614915718135)⟩, true⟩

def words09 : List Nat := [360582093276990329, 360582093318731868, 360582093357848377, 360582093359215721, 360582093309302507, 360582093158031755, 360582093006502068, 360582092982999345, 360582093111723980, 360582093240758185]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk943B
