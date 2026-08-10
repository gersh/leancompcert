import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk956A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk956B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk956A

def state06 : KState := ⟨⟨362501603945735872, 362501743069204380⟩, ⟨(-1588048557143821465), (-1579063143115497405)⟩, true⟩

def words05 : List Nat := [371285234962695221, 371285235093409103, 371285235305082633, 371285235416830827, 371285235499122597, 371285235582467307, 371285235743025648, 371285235853797628, 371285236028638605, 371285236204932467]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491536555726499, 362491675709508332⟩, ⟨(-624946892520117824), (-615958578562425076)⟩, true⟩

def words06 : List Nat := [371285236380130846, 371285236465495379, 371285236649471652, 371285236835229953, 371285237041458653, 371285237125329491, 371285237182963611, 371285237241670629, 371285237338565966, 371285237409725092]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487257594201548, 362487396778228678⟩, ⟨(-215534506796668027), (-206543299122081849)⟩, true⟩

def words07 : List Nat := [371285237559635673, 371285237710937138, 371285237860641473, 371285237865509689, 371285237888577473, 371285237913345717, 371285238035460264, 371285238060967863, 371285238086059568, 371285238112463040]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490226566432773, 362490365780497430⟩, ⟨(-499596395778089575), (-490602313957650197)⟩, true⟩

def words08 : List Nat := [371285238232134618, 371285238302052129, 371285238415687230, 371285238530624044, 371285238628186990, 371285238631541351, 371285238628181089, 371285238677307076, 371285238780266736, 371285238837378875]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488168719802322, 362488307964379251⟩, ⟨(-302667754008930720), (-293670752318926570)⟩, true⟩

def words09 : List Nat := [371285238891283705, 371285238946292239, 371285239045405460, 371285239096455697, 371285239178969777, 371285239262812522, 371285239330131095, 371285239333486681, 371285239300324673, 371285239336545489]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk956B
