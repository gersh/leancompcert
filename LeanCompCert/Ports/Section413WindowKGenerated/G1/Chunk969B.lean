import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk969A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk969B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk969A

def state06 : KState := ⟨⟨362491802222750618, 362491945301929394⟩, ⟨(-651086539488828817), (-641720144534541067)⟩, true⟩

def words05 : List Nat := [371285326270890439, 371285326283874805, 371285326401970933, 371285326498835792, 371285326626236638, 371285326754908287, 371285326861118479, 371285326864520299, 371285326896830886, 371285326969357179]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 96950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 96900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480261991368156, 362480405100837275⟩, ⟨467926789597407753, 477296121660865777⟩, true⟩

def words06 : List Nat := [371285327128956286, 371285327147814362, 371285327165420406, 371285327184209233, 371285327187192986, 371285327190977529, 371285327157868651, 371285327178817687, 371285327198188183, 371285327201710338]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 96960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 96900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493897680143532, 362494040820377509⟩, ⟨(-854419397278999856), (-845047081791977496)⟩, true⟩

def words07 : List Nat := [371285327153299496, 371285327149807604, 371285327243536989, 371285327246939245, 371285327206752698, 371285327150546636, 371285327114998125, 371285327118813229, 371285327194359731, 371285327288017645]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 96970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 96900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481819188756399, 362481962359641525⟩, ⟨316974362002337242, 326349650194194048⟩, true⟩

def words08 : List Nat := [371285327380036778, 371285327383439361, 371285327380665940, 371285327432025328, 371285327464066387, 371285327467469610, 371285327371925109, 371285327258149325, 371285327143020637, 371285327135909122]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 96980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 96900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476912417707795, 362477055619308602⟩, ⟨792933705272846634, 802311972733328328⟩, true⟩

def words09 : List Nat := [371285327145096972, 371285327190471921, 371285327232784454, 371285327236187651, 371285327136580519, 371285327063493497, 371285327017977807, 371285327021404427, 371285326958170617, 371285326876759462]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 96990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 96900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 96900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk969B
