import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk862A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk862B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk862A

def state06 : KState := ⟨⟨362474927983236696, 362475040208004088⟩, ⟨871243808708956963, 877780164948354923⟩, true⟩

def words05 : List Nat := [371285217047503277, 371285216985258872, 371285216922029882, 371285216859725835, 371285216696878107, 371285216560588153, 371285216422670938, 371285216419984673, 371285216304133528, 371285216189512880]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484819700631444, 362484931952274933⟩, ⟨17947295418454656, 24485970125702882⟩, true⟩

def words06 : List Nat := [371285216073615459, 371285216014533266, 371285215932063025, 371285215960209504, 371285215965438823, 371285215968439008, 371285215794287178, 371285215746087748, 371285215778658974, 371285215781765205]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473024690452848, 362473136969439622⟩, ⟨1035569246183917523, 1042110279934621753⟩, true⟩

def words07 : List Nat := [371285215780717769, 371285215776401834, 371285215798746560, 371285215802084227, 371285215764988757, 371285215701501891, 371285215637029923, 371285215573448616, 371285215342587282, 371285215206341971]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471134689213064, 362471246994949878⟩, ⟨1198677007721028384, 1205220349604944706⟩, true⟩

def words08 : List Nat := [371285215068399204, 371285215020669158, 371285214860712206, 371285214701850085, 371285214541844372, 371285214424193845, 371285214246140822, 371285214203506542, 371285214159859679, 371285214086728821]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497489736128507, 362497602068974624⟩, ⟨(-1075627897885620949), (-1069082216606744961)⟩, true⟩

def words09 : List Nat := [371285213926903352, 371285213902798946, 371285213983555964, 371285213986571523, 371285213966931602, 371285213908470988, 371285213921029285, 371285213945344448, 371285214090926805, 371285214237818476]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk862B
