import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk892A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk892B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk892A

def state06 : KState := ⟨⟨362475398164208216, 362475518647895762⟩, ⟨852021815893820940, 859283051667930374⟩, true⟩

def words05 : List Nat := [371285145526257061, 371285145595676991, 371285145657125579, 371285145660258632, 371285145609027600, 371285145597703984, 371285145597256940, 371285145600383893, 371285145494960761, 371285145390576335]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482761928824558, 362482882440370147⟩, ⟨194734224874737288, 201997947395760258⟩, true⟩

def words06 : List Nat := [371285145302371184, 371285145305847443, 371285145358377018, 371285145432165988, 371285145464847351, 371285145467959612, 371285145333133499, 371285145252861856, 371285145212406607, 371285145215629426]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491149356039020, 362491269896042842⟩, ⟨(-554057437095423982), (-546791173970106874)⟩, true⟩

def words07 : List Nat := [371285145192683163, 371285145154711696, 371285145199418238, 371285145224206230, 371285145285536889, 371285145348051034, 371285145409413190, 371285145412581136, 371285145438984966, 371285145511526875]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476003909702723, 362476124477403303⟩, ⟨798207945126657007, 805476681164825057⟩, true⟩

def words08 : List Nat := [371285145643705552, 371285145646818338, 371285145612061213, 371285145578259425, 371285145543306463, 371285145515590216, 371285145434033672, 371285145418079096, 371285145401069519, 371285145383228870]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487369590993695, 362487490186856801⟩, ⟨(-216674812854155927), (-209403562042942569)⟩, true⟩

def words09 : List Nat := [371285145284313604, 371285145280827681, 371285145393740356, 371285145396853694, 371285145350207895, 371285145284746742, 371285145232597026, 371285145236085727, 371285145238671482, 371285145268411958]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk892B
