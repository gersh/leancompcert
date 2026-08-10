import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk560A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk560B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk560A

def state06 : KState := ⟨⟨362493208648210020, 362493254478973200⟩, ⟨(-468390280496634349), (-466654661755911227)⟩, true⟩

def words05 : List Nat := [371284930385676769, 371284930385673474, 371284930700474956, 371284930702362094, 371284930595592338, 371284930400480920, 371284930244188878, 371284930246268399, 371284930276697511, 371284930427283864]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362465286501269439, 362465332349104265⟩, ⟨1097020382373655313, 1098756958235692813⟩, true⟩

def words06 : List Nat := [371284930577182423, 371284930579069855, 371284930304977727, 371284930163662838, 371284930021392606, 371284929976507371, 371284929622186726, 371284929209461011, 371284928796008788, 371284928513866807]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362458912053048031, 362458957917873541⟩, ⟨1454545853130790742, 1456283381748436038⟩, true⟩

def words07 : List Nat := [371284928165659613, 371284928086737656, 371284928007164551, 371284927928054821, 371284927539042566, 371284927245529667, 371284926951092765, 371284926789071490, 371284926342086540, 371284925881171481]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476567896235287, 362476613777962403⟩, ⟨464385635231499782, 466124111776708556⟩, true⟩

def words08 : List Nat := [371284925419408525, 371284925276150212, 371284925015002274, 371284924952363659, 371284924889122052, 371284924776333860, 371284924319595805, 371284924181516151, 371284924065039025, 371284924066993901]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486769640949101, 362486815539887855⟩, ⟨(-107893835366519020), (-106154393334477496)⟩, true⟩

def words09 : List Nat := [371284923920273191, 371284923710107195, 371284923604568662, 371284923606649518, 371284923560173107, 371284923567823844, 371284923569251207, 371284923551158396, 371284923302370913, 371284923338441634]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk560B
