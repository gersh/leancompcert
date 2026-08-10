import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk605A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk605B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk605A

def state06 : KState := ⟨⟨360612106732193937, 360612130098549529⟩, ⟨(-1803929165065348569), (-1802973196035889811)⟩, true⟩

def words05 : List Nat := [360582355162696337, 360582355570089874, 360582356095304277, 360582356686593311, 360582357004917098, 360582357323291412, 360582357554035916, 360582357921156654, 360582358413457441, 360582358905933227]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608953864022641, 360608977238456265⟩, ⟨(-1613109315449773700), (-1612152857175072082)⟩, true⟩

def words06 : List Nat := [360582359259867117, 360582359403086259, 360582359738291800, 360582360073751497, 360582360339373288, 360582360563166977, 360582360615148243, 360582360667217142, 360582360878603490, 360582361319003473]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571118548542624, 360571141930971436⟩, ⟨678739907572713489, 679696850156242975⟩, true⟩

def words07 : List Nat := [360582361643570553, 360582361968277465, 360582362127260709, 360582362128109363, 360582362126880428, 360582362057385155, 360582361987648011, 360582361959407004, 360582361937850553, 360582361753522712]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602946196877656, 360602969587308723⟩, ⟨(-1249552955395120776), (-1248595527996684200)⟩, true⟩

def words08 : List Nat := [360582361569005172, 360582361668594545, 360582361990501616, 360582362312560437, 360582362371112147, 360582362371960357, 360582362158846213, 360582362115305376, 360582362299287518, 360582362640270439]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569578272667014, 360569601671182998⟩, ⟨772421383902646679, 773379301206915753⟩, true⟩

def words09 : List Nat := [360582362817329268, 360582362994488175, 360582363152306702, 360582363446288970, 360582363670556462, 360582363894955113, 360582363983023875, 360582363983872633, 360582363915485815, 360582363705856380]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk605B
