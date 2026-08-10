import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk685A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk685B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk685A

def state06 : KState := ⟨⟨362479198673645529, 362479268319221312⟩, ⟨421215888178479294, 424440757944564600⟩, true⟩

def words05 : List Nat := [371285459548611160, 371285459615380036, 371285459680591916, 371285459682935547, 371285459486854363, 371285459356714317, 371285459286105234, 371285459288490614, 371285459199707582, 371285459112073479]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480205001500928, 362480274668038158⟩, ⟨352216265518223726, 355442572509776598⟩, true⟩

def words06 : List Nat := [371285459023372348, 371285459025787169, 371285458950530899, 371285458938008158, 371285458924808159, 371285458862943910, 371285458516977725, 371285458384667985, 371285458311119930, 371285458313546541]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477296730605392, 362477366418536897⟩, ⟨551699013712079926, 554926787816009898⟩, true⟩

def words07 : List Nat := [371285458239723635, 371285458158101220, 371285458169517469, 371285458192169331, 371285458248765204, 371285458306280791, 371285458363247905, 371285458365598858, 371285458204483810, 371285458089400356]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474894273500928, 362474963982306783⟩, ⟨716491066210398147, 719720271985649609⟩, true⟩

def words08 : List Nat := [371285458067342923, 371285458069688210, 371285457914438907, 371285457760289165, 371285457605238270, 371285457433811621, 371285457197133392, 371285457152164055, 371285457106429611, 371285457061064411]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489376072867313, 362489445802924681⟩, ⟨(-276912457525638277), (-273681794004177189)⟩, true⟩

def words09 : List Nat := [371285456953191359, 371285456999544434, 371285457085454423, 371285457087799707, 371285456890799522, 371285456639411920, 371285456387081458, 371285456347990537, 371285456269693460, 371285456330555413]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk685B
