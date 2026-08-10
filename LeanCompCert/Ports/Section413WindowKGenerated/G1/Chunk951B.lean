import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk951A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk951B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk951A

def state06 : KState := ⟨⟨362494048196025601, 362494185813488876⟩, ⟨(-862993295606138734), (-854151570018556958)⟩, true⟩

def words05 : List Nat := [371285209222482848, 371285209241232866, 371285209369137803, 371285209443432612, 371285209549601522, 371285209657016276, 371285209753937882, 371285209760951498, 371285209857539433, 371285209956047083]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482557621295053, 362482695268435611⟩, ⟨230490227396439638, 239334777229140412⟩, true⟩

def words06 : List Nat := [371285210086328240, 371285210089663439, 371285210072926309, 371285210056918660, 371285210039702316, 371285210030032802, 371285210006790631, 371285210043282151, 371285210078232130, 371285210081687993]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362494689986175432, 362494827663469427⟩, ⟨(-924202731116636433), (-915355311429361461)⟩, true⟩

def words07 : List Nat := [371285210112096211, 371285210170713756, 371285210300330343, 371285210311659177, 371285210314270849, 371285210307734161, 371285210400123984, 371285210459209772, 371285210562553319, 371285210667310222]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489031263932504, 362489168971329178⟩, ⟨(-385643997476832133), (-376793712462584857)⟩, true⟩

def words08 : List Nat := [371285210770489752, 371285210773825809, 371285210729632007, 371285210715269133, 371285210713942352, 371285210717353166, 371285210669703702, 371285210622811437, 371285210634575145, 371285210679973246]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484352801887237, 362484490539404943⟩, ⟨59774729698384041, 68627882081542415⟩, true⟩

def words09 : List Nat := [371285210834282277, 371285210989977425, 371285211122342939, 371285211156861830, 371285211219580252, 371285211283912454, 371285211425832546, 371285211429169396, 371285211424212392, 371285211420519245]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk951B
