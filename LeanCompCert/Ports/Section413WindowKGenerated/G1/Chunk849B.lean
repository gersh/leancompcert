import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk849A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk849B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk849A

def state06 : KState := ⟨⟨362465947111015700, 362466055851262960⟩, ⟨1630065246130671541, 1636303286054613169⟩, true⟩

def words05 : List Nat := [371285316736313084, 371285316613451795, 371285316489319989, 371285316437837140, 371285316316015664, 371285316220958013, 371285316124932015, 371285316029604325, 371285315764498746, 371285315541541381]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470222590467541, 362470331357010186⟩, ⟨1266811748749738853, 1273052022863439503⟩, true⟩

def words06 : List Nat := [371285315316854252, 371285315231538075, 371285314995939590, 371285314750281081, 371285314503502729, 371285314300415403, 371285314052685319, 371285313944609750, 371285313835512735, 371285313727527586]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482396574800556, 362482505368016237⟩, ⟨232304754631021728, 238547295288802530⟩, true⟩

def words07 : List Nat := [371285313553207516, 371285313497188013, 371285313439705803, 371285313432939709, 371285313240962206, 371285313003702092, 371285312765205777, 371285312666360232, 371285312496965062, 371285312467278285]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468516620444284, 362468625440263657⟩, ⟨1411851466742870429, 1418096268322048805⟩, true⟩

def words08 : List Nat := [371285312436463191, 371285312404586886, 371285312187233274, 371285312058938791, 371285311929163522, 371285311816672060, 371285311579185421, 371285311313452656, 371285311046552048, 371285310888767270]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362464632533080813, 362464741379522029⟩, ⟨1742054475162300987, 1748301539463628379⟩, true⟩

def words09 : List Nat := [371285310694449190, 371285310639702129, 371285310583916994, 371285310518535348, 371285310371609471, 371285310257901817, 371285310142675108, 371285310099717381, 371285309871551932, 371285309632927484]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk849B
