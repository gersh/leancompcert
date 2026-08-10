import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk939A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk939B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk939A

def state06 : KState := ⟨⟨362486157071001423, 362486291107753990⟩, ⟨(-115353721935798480), (-106850593792514084)⟩, true⟩

def words05 : List Nat := [371285153492747316, 371285153515851684, 371285153632524753, 371285153709492257, 371285153790303615, 371285153872335782, 371285153953019790, 371285153956309933, 371285153911244451, 371285153927500561]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482164380538230, 362482298446623636⟩, ⟨259820297980828379, 268326182392172959⟩, true⟩

def words06 : List Nat := [371285153980901806, 371285153984214282, 371285153936460768, 371285153889548865, 371285153841389386, 371285153829035392, 371285153799589290, 371285153844069085, 371285153888384850, 371285153891791160]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497920552812581, 362498054648586920⟩, ⟨(-1220869902898881483), (-1212361228467857663)⟩, true⟩

def words07 : List Nat := [371285153946526101, 371285154033319256, 371285154176071514, 371285154202769484, 371285154205362761, 371285154204624882, 371285154273142488, 371285154300819188, 371285154440316923, 371285154581249184]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488886152412401, 362489020277912119⟩, ⟨(-371763043987308492), (-363251575816760130)⟩, true⟩

def words08 : List Nat := [371285154720711991, 371285154771048700, 371285154933513671, 371285155097758711, 371285155294761065, 371285155341856965, 371285155379882571, 371285155418963860, 371285155484525375, 371285155529416873]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481151553688965, 362481285708853522⟩, ⟨355285074046226103, 363799330564311507⟩, true⟩

def words09 : List Nat := [371285155679943278, 371285155831839240, 371285155956867488, 371285155960158683, 371285155934182258, 371285155916010800, 371285155987094599, 371285155990387176, 371285155951922232, 371285155914497824]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk939B
