import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk613A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk613B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk613A

def state06 : KState := ⟨⟨362485251444972593, 362485306746615265⟩, ⟨(-341115565991703), 1950945813163695⟩, true⟩

def words05 : List Nat := [371285337781076123, 371285338122827994, 371285338427687933, 371285338429767841, 371285338380488967, 371285338347488829, 371285338543733843, 371285338545827942, 371285338539832521, 371285338541690447]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497549205322356, 362497604525603341⟩, ⟨(-754913181386651000), (-752619976265588874)⟩, true⟩

def words06 : List Nat := [371285338757395918, 371285338880264620, 371285339267909445, 371285339656374131, 371285340003888399, 371285340036560965, 371285340306491421, 371285340577509231, 371285340877093280, 371285341079085188]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498958708667240, 362499014047903685⟩, ⟨(-841406314582696791), (-839111946073650983)⟩, true⟩

def words07 : List Nat := [371285341278590399, 371285341478756844, 371285341853001457, 371285342109276117, 371285342443266980, 371285342778111341, 371285343090592983, 371285343092673614, 371285343273947461, 371285343499263656]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489710795831015, 362489766153607835⟩, ⟨(-273690749815858723), (-271395243201066333)⟩, true⟩

def words08 : List Nat := [371285343988969638, 371285344174832917, 371285344296566584, 371285344418988996, 371285344620549637, 371285344722792305, 371285344923652663, 371285345125328305, 371285345313442584, 371285345387645381]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493907743133217, 362493963119726774⟩, ⟨(-531361154240090644), (-529064492369703900)⟩, true⟩

def words09 : List Nat := [371285345596662814, 371285345806770237, 371285346196203031, 371285346232692289, 371285346234302891, 371285346230727625, 371285346322334742, 371285346324651972, 371285346431823823, 371285346574517907]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk613B
