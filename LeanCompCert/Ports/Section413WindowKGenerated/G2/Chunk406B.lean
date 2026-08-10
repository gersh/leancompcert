import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk406A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk406B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk406A

def state06 : KState := ⟨⟨360574366348453707, 360574376545304866⟩, ⟨332813516471505902, 333093729061584004⟩, true⟩

def words05 : List Nat := [360582566411757030, 360582567515822548, 360582568315771372, 360582568513450194, 360582568513912008, 360582568456775259, 360582568816061688, 360582568918108325, 360582568918599786, 360582568717687099]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589051031007750, 360589061233074880⟩, ⟨(-264383574601797216), (-264103149904752654)⟩, true⟩

def words06 : List Nat := [360582568746581110, 360582569298736289, 360582569642940478, 360582569987230202, 360582569987738904, 360582569818586652, 360582569047407211, 360582568368232081, 360582567688928916, 360582567585269202]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593199236246957, 360593209443572156⟩, ⟨(-433120575477977971), (-432839936909252407)⟩, true⟩

def words07 : List Nat := [360582567585765406, 360582567442495381, 360582567602882328, 360582568209719364, 360582568664884985, 360582569120117675, 360582569120620225, 360582569067074906, 360582569326493960, 360582569588678981]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360556651743091392, 360556661955614370⟩, ⟨1053743469608960029, 1054024319649408993⟩, true⟩

def words08 : List Nat := [360582570055148690, 360582570055700710, 360582569920717301, 360582569424434847, 360582568928077438, 360582568169467051, 360582567712909577, 360582567207740728, 360582566702544867, 360582565723607720]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360606617850037748, 360606628067780665⟩, ⟨(-979819488977761651), (-979538426512816697)⟩, true⟩

def words09 : List Nat := [360582565087465056, 360582564436410679, 360582563785226712, 360582563736460995, 360582563086474199, 360582561924544303, 360582560762565934, 360582560203035895, 360582560783997666, 360582561375893173]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk406B
