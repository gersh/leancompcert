import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk637A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk637B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk637A

def state06 : KState := ⟨⟨362482298468066905, 362482358361316389⟩, ⟨193097971046134691, 195677321495079443⟩, true⟩

def words05 : List Nat := [371285426479445531, 371285426780943895, 371285427080922437, 371285427083089907, 371285427119081894, 371285427157125565, 371285427411615784, 371285427413783581, 371285427373760147, 371285427328090152]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484379824725728, 362484439737391034⟩, ⟨60427861999881964, 63008450503067352⟩, true⟩

def words06 : List Nat := [371285427479499495, 371285427557476271, 371285427736061641, 371285427915482607, 371285428082564948, 371285428084732690, 371285427923790342, 371285427814340187, 371285427792980147, 371285427795263123]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490807156213742, 362490867088603836⟩, ⟨(-349451562776682043), (-346869716321548393)⟩, true⟩

def words07 : List Nat := [371285427781391666, 371285427751924013, 371285427935899682, 371285428031011761, 371285428199793064, 371285428369427763, 371285428491284551, 371285428493477776, 371285428551663903, 371285428639593605]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482605920998952, 362482665872684138⟩, ⟨173703287690160463, 176286364886867133⟩, true⟩

def words08 : List Nat := [371285428972387934, 371285428978212641, 371285428979852581, 371285428972854735, 371285429029914258, 371285429032303731, 371285429135952574, 371285429297864547, 371285429412764067, 371285429415008748]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505673942924477, 362505733914270771⟩, ⟨(-1297970105372786857), (-1295385773898911833)⟩, true⟩

def words09 : List Nat := [371285429391989644, 371285429413436215, 371285429679677510, 371285429681846331, 371285429650114967, 371285429581773925, 371285429665071844, 371285429739819084, 371285430059537750, 371285430380252513]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk637B
