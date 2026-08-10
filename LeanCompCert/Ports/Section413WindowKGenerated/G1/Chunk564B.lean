import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk564A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk564B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk564A

def state06 : KState := ⟨⟨362465877475612922, 362465923989171538⟩, ⟨1069150707997850792, 1070924741052043370⟩, true⟩

def words05 : List Nat := [371284892927031413, 371284892752579315, 371284892714422599, 371284892716517992, 371284892704458397, 371284892708434440, 371284892709875550, 371284892649993609, 371284892171557453, 371284891837932644]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362460135602484953, 362460182133002319⟩, ⟨1393423974454690684, 1395198965088953466⟩, true⟩

def words06 : List Nat := [371284891503277023, 371284891451060892, 371284891183120291, 371284890813887600, 371284890443917482, 371284890112610093, 371284889624030206, 371284889449636388, 371284889274644933, 371284889038706037]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362505256994987680, 362505303542722775⟩, ⟨(-1154801646101627515), (-1153025683095565355)⟩, true⟩

def words07 : List Nat := [371284888602481872, 371284888441259280, 371284888428870952, 371284888430791455, 371284888376139988, 371284888269571222, 371284888366886920, 371284888417132243, 371284888779880712, 371284889143489484]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483638750200209, 362483685315119012⟩, ⟨66223118882951279, 68000052512049491⟩, true⟩

def words08 : List Nat := [371284889483937530, 371284889485841673, 371284889589278333, 371284889707215196, 371284889820872333, 371284889822775558, 371284889565302899, 371284889295649472, 371284889066717304, 371284889068925209]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472377655889774, 362472424237922942⟩, ⟨702472875001472077, 704250775507076605⟩, true⟩

def words09 : List Nat := [371284889222873945, 371284889398879842, 371284889574603879, 371284889576507831, 371284889393928498, 371284889307717492, 371284889262240118, 371284889264153934, 371284889071912856, 371284888853418643]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk564B
