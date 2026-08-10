import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk978A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk978B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk978A

def state06 : KState := ⟨⟨362493130745385168, 362493276596390646⟩, ⟨(-785832979861807940), (-776196578803677486)⟩, true⟩

def words05 : List Nat := [371285344227959646, 371285344306851302, 371285344426758994, 371285344503485897, 371285344610413911, 371285344718732067, 371285344824442221, 371285344827878299, 371285344887839114, 371285344973182181]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477309578483978, 362477455460068309⟩, ⟨762552183771564441, 772191577435896791⟩, true⟩

def words06 : List Nat := [371285345161031645, 371285345222516881, 371285345282941377, 371285345344574777, 371285345408533981, 371285345421763491, 371285345430345549, 371285345440237538, 371285345442818343, 371285345432250141]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499056278655978, 362499202191325265⟩, ⟨(-1365903219507013819), (-1356260783398265969)⟩, true⟩

def words07 : List Nat := [371285345377799177, 371285345405793878, 371285345518796491, 371285345546154963, 371285345554237186, 371285345563325712, 371285345639862544, 371285345680812182, 371285345824708486, 371285345970164895]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489761130596476, 362489907074335609⟩, ⟨(-456074875038670961), (-446429397659410111)⟩, true⟩

def words08 : List Nat := [371285346092206308, 371285346095643464, 371285346187538918, 371285346288646559, 371285346419608682, 371285346444642402, 371285346461938704, 371285346480524410, 371285346549426009, 371285346599954314]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482795573276342, 362482941547878048⟩, ⟨225852392135917734, 235500890812924164⟩, true⟩

def words09 : List Nat := [371285346738184875, 371285346877780904, 371285347013176232, 371285347016613706, 371285347012777762, 371285347016730369, 371285347111910751, 371285347115351035, 371285347093520318, 371285347072809743]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk978B
