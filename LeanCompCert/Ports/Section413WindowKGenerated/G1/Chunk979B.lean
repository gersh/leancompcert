import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk979A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk979B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk979A

def state06 : KState := ⟨⟨362480086184316321, 362480232344855566⟩, ⟨491459391318926779, 501126098867976419⟩, true⟩

def words05 : List Nat := [371285348018488938, 371285348074899899, 371285348127903657, 371285348131354563, 371285348098670025, 371285348062319772, 371285348058773835, 371285348062273771, 371285348012806646, 371285347964484680]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362499412680471575, 362499558871790243⟩, ⟨(-1401840299958385377), (-1392170577102355879)⟩, true⟩

def words06 : List Nat := [371285347966637858, 371285347980168106, 371285348083610938, 371285348188429633, 371285348267333967, 371285348271480421, 371285348378741374, 371285348487852308, 371285348695960005, 371285348844566857]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495367758650991, 362495513981293463⟩, ⟨(-1005503263845078387), (-995830472036616777)⟩, true⟩

def words07 : List Nat := [371285348981639829, 371285349119899079, 371285349360955865, 371285349551465427, 371285349772619813, 371285349995118560, 371285350197223478, 371285350261321214, 371285350367427220, 371285350475388884]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491877297447144, 362492023550742748⟩, ⟨(-663494791107449285), (-653818995746022435)⟩, true⟩

def words08 : List Nat := [371285350650112276, 371285350687087998, 371285350721318978, 371285350756729527, 371285350822255398, 371285350851363097, 371285350983144138, 371285351116328607, 371285351243925726, 371285351315580886]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496245617051734, 362496391901537409⟩, ⟨(-1091560677667158976), (-1081881825837498618)⟩, true⟩

def words09 : List Nat := [371285351448114704, 371285351582497496, 371285351758149942, 371285351835338076, 371285351894565081, 371285351954831323, 371285352088714206, 371285352172081774, 371285352287081771, 371285352403717617]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk979B
