import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk880A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk880B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk880A

def state06 : KState := ⟨⟨362474870830873612, 362474987974481438⟩, ⟨892321279508992737, 899286378729381819⟩, true⟩

def words05 : List Nat := [371285200274084152, 371285200409975977, 371285200516848987, 371285200519916324, 371285200454755984, 371285200397042240, 371285200395830433, 371285200398897879, 371285200287493348, 371285200175012092]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486497882931463, 362486615053978563⟩, ⟨(-131573262186587092), (-124605746524693568)⟩, true⟩

def words06 : List Nat := [371285200061124840, 371285200064216121, 371285200086439785, 371285200158609272, 371285200215102034, 371285200218190837, 371285200158842252, 371285200131972510, 371285200201857898, 371285200221099129]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487577088925592, 362487694287962197⟩, ⟨(-226612999028551002), (-219643018192093080)⟩, true⟩

def words07 : List Nat := [371285200239476631, 371285200258916642, 371285200373615232, 371285200441552165, 371285200532548528, 371285200624678478, 371285200674733992, 371285200677803390, 371285200607707388, 371285200639863378]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478198225238707, 362478315451635047⟩, ⟨599510706005309699, 606483096826375167⟩, true⟩

def words08 : List Nat := [371285200723854017, 371285200726922504, 371285200639353373, 371285200553147225, 371285200465787233, 371285200407591396, 371285200291930384, 371285200282997718, 371285200272902592, 371285200263722985]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494374976186242, 362494492230268767⟩, ⟨(-825554561155644656), (-818579731314570798)⟩, true⟩

def words09 : List Nat := [371285200225916005, 371285200267856730, 371285200436950385, 371285200475178543, 371285200480596979, 371285200486973353, 371285200592713874, 371285200635386704, 371285200742948371, 371285200851835894]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk880B
