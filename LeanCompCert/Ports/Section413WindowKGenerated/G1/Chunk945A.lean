import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk945A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493330032113822, 362493465674110134⟩, ⟨(-792110775527642464), (-783456384589581748)⟩, true⟩

def state01 : KState := ⟨⟨362478030697935706, 362478166369377492⟩, ⟨653746493572005630, 662403667263499914⟩, true⟩

def words00 : List Nat := [371285175357088600, 371285175360398974, 371285175350356546, 371285175328754958, 371285175305856452, 371285175302336081, 371285175253990047, 371285175233027076, 371285175210998973, 371285175190319864]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 94500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 94500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500178146272280, 362500313847672519⟩, ⟨(-1439516422863496464), (-1430856417650471708)⟩, true⟩

def words01 : List Nat := [371285175126945929, 371285175139518657, 371285175262332036, 371285175305971209, 371285175331585822, 371285175358201669, 371285175477449631, 371285175547590272, 371285175709996580, 371285175873913773]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 94510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 94500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486249100088115, 362486384831393520⟩, ⟨(-122933941561199889), (-114271109559974305)⟩, true⟩

def words02 : List Nat := [371285176014717237, 371285176019638074, 371285176058678720, 371285176099374500, 371285176166704477, 371285176170015881, 371285176098888882, 371285176028072608, 371285175993276208, 371285176009847573]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 94520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 94500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477855548473327, 362477991309546278⟩, ⟨670612732653341528, 679278378732772538⟩, true⟩

def words03 : List Nat := [371285176136874789, 371285176265218087, 371285176392117713, 371285176419833336, 371285176441906273, 371285176465662114, 371285176541409533, 371285176544721431, 371285176471538361, 371285176399230357]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 94530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 94500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488004816991607, 362488140607739794⟩, ⟨(-288893807421595038), (-280225355693215174)⟩, true⟩

def words04 : List Nat := [371285176361448088, 371285176365161887, 371285176470026609, 371285176580963286, 371285176660737289, 371285176664050950, 371285176672436711, 371285176735414947, 371285176824761258, 371285176859543655]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 94540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 94500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk945A
