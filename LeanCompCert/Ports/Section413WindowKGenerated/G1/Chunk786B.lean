import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk786A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk786B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk786A

def state06 : KState := ⟨⟨362480261335297866, 362480353996211016⟩, ⟨378889669309084838, 383811554438055458⟩, true⟩

def words05 : List Nat := [371285233017502043, 371285233000680323, 371285233124478496, 371285233188447905, 371285233300882120, 371285233414392961, 371285233516468807, 371285233519185100, 371285233428809720, 371285233370155055]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 78650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 78600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473638622092377, 362473731307169597⟩, ⟨899869564897645773, 904793350901705433⟩, true⟩

def words06 : List Nat := [371285233331156466, 371285233333873922, 371285233170163024, 371285233005748527, 371285232840273598, 371285232725492121, 371285232550488258, 371285232510878117, 371285232470394977, 371285232430226693]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 78660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 78600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483082763238177, 362483175472959634⟩, ⟨156862936892210590, 161788661777623576⟩, true⟩

def words07 : List Nat := [371285232285876433, 371285232287275006, 371285232352320949, 371285232355037531, 371285232223789722, 371285232068592234, 371285231912297142, 371285231878244858, 371285231782971947, 371285231759967484]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 78670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 78600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362459964540700403, 362460057274899744⟩, ⟨1975878237214716608, 1980805888147616852⟩, true⟩

def words08 : List Nat := [371285231735863690, 371285231712375223, 371285231472808772, 371285231283906256, 371285231093693747, 371285230953851920, 371285230598184554, 371285230211721821, 371285229824133430, 371285229544414900]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 78680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 78600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467896792894202, 362467989551526812⟩, ⟨1351704869047229418, 1356634442758820560⟩, true⟩

def words09 : List Nat := [371285229226370226, 371285229070797078, 371285228914340102, 371285228738252813, 371285228480330987, 371285228273368939, 371285228064948201, 371285228018774001, 371285227816361494, 371285227600354752]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 78690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 78600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 78600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk786B
