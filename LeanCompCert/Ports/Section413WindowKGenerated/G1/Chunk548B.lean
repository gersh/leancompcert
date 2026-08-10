import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk548A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk548B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk548A

def state06 : KState := ⟨⟨362488936110817544, 362488979924434907⟩, ⟨(-224717894588679572), (-223094151502075982)⟩, true⟩

def words05 : List Nat := [371284912229332792, 371284912494892480, 371284913006238119, 371284913075494810, 371284913076937930, 371284913069767948, 371284913222562323, 371284913238298321, 371284913313703592, 371284913389893028]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485879795899885, 362485923626157519⟩, ⟨(-57109915239549711), (-55485259185169805)⟩, true⟩

def words06 : List Nat := [371284913465838884, 371284913467683504, 371284913100974608, 371284913040731102, 371284913018563718, 371284913020440476, 371284912784973653, 371284912550634122, 371284912411017381, 371284912431552260]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472318979566407, 362472362826484104⟩, ⟨687098878453173694, 688724448727905754⟩, true⟩

def words07 : List Nat := [371284912707173978, 371284912983555597, 371284913185098505, 371284913186943698, 371284912946042610, 371284912807900228, 371284912860182868, 371284912862030862, 371284912696771564, 371284912470229147]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493690973673286, 362493734837089553⟩, ⟨(-485854422750107312), (-484227946946777532)⟩, true⟩

def words08 : List Nat := [371284912345815822, 371284912347868097, 371284912512468266, 371284912740140151, 371284912914104536, 371284912915958863, 371284912771956977, 371284912766419287, 371284913047100211, 371284913209738134]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485151495203982, 362485195375428330⟩, ⟨(-17021728551225198), (-15394330068432572)⟩, true⟩

def words09 : List Nat := [371284913358291845, 371284913507428773, 371284913863409763, 371284914100789471, 371284914438837174, 371284914777603854, 371284915089550723, 371284915091396778, 371284914966398623, 371284914973795055]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk548B
