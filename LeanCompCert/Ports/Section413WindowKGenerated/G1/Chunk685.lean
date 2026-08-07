import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk685

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475313087699011, 362475382606640015⟩, ⟨686839966708150668, 690056158182345986⟩, true⟩

def state01 : KState := ⟨⟨362491720326633163, 362491789866561195⟩, ⟨(-437085335345384393), (-433867706153561893)⟩, true⟩

def words00 : List Nat := [371285456339469770, 371285456342095487, 371285456499565292, 371285456671830495, 371285456809461656, 371285456811803294, 371285456730127628, 371285456797713835, 371285456953503194, 371285457048383771]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 68500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 68500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488301258448376, 362488370819719651⟩, ⟨(-202784289934686460), (-199565198407583992)⟩, true⟩

def words01 : List Nat := [371285457118105719, 371285457188648940, 371285457451482271, 371285457634065270, 371285457871182917, 371285458109213281, 371285458327447553, 371285458329789836, 371285458306604539, 371285458352032262]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 68510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 68500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481111077140382, 362481180659313068⟩, ⟨289930911013728726, 293151434812966130⟩, true⟩

def words02 : List Nat := [371285458608825843, 371285458611168189, 371285458584438601, 371285458524185573, 371285458465936294, 371285458468544997, 371285458381766232, 371285458379475842, 371285458376364137, 371285458368853605]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 68520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 68500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362497994884891107, 362498064488173202⟩, ⟨(-867190671304947104), (-863968700767544294)⟩, true⟩

def words03 : List Nat := [371285458458254321, 371285458611259366, 371285458919430117, 371285458944720292, 371285458946550076, 371285458937469633, 371285459005162666, 371285459007744281, 371285459164567674, 371285459351090762]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 68530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 68500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484039520223173, 362484109144661826⟩, ⟨89343609728885585, 92567030438141235⟩, true⟩

def words04 : List Nat := [371285459495326935, 371285459497671162, 371285459501250908, 371285459611455009, 371285459785178025, 371285459787521422, 371285459677824577, 371285459572794812, 371285459499833306, 371285459502509210]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 68540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 68500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk685
