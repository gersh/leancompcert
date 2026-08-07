import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk339

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362503341954454038, 362503358041502337⟩, ⟨(-632557493103609225), (-632188910438520035)⟩, true⟩

def state01 : KState := ⟨⟨362486437356443249, 362486453453279705⟩, ⟨(-59371650475637695), (-59002735941333203)⟩, true⟩

def words00 : List Nat := [371284710676257438, 371284710836363488, 371284710996506565, 371284711157022388, 371284711582748694, 371284711583957438, 371284712220850280, 371284712866290326, 371284713471726569, 371284713524172887]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 33900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 33900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362520470810639752, 362520486917409604⟩, ⟨(-1213600899676254266), (-1213231648251354930)⟩, true⟩

def words01 : List Nat := [371284714445962266, 371284715368287347, 371284716735419867, 371284717127996923, 371284717275087871, 371284717422483099, 371284718136577704, 371284718418458649, 371284719473700150, 371284720529382973]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 33910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 33900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489671876683163, 362489687993379982⟩, ⟨(-168729864327025777), (-168360276129070583)⟩, true⟩

def words02 : List Nat := [371284721585710985, 371284721923812618, 371284723130664271, 371284724338008885, 371284725575307589, 371284725655114976, 371284725697577644, 371284725740417318, 371284726003423034, 371284726150931217]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 33920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 33900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487739283573079, 362487755410150070⟩, ⟨(-103008559383353124), (-102638635900632620)⟩, true⟩

def words03 : List Nat := [371284727166735481, 371284728182919025, 371284729196759226, 371284729430741393, 371284729695982668, 371284729961782190, 371284731095535095, 371284731198900734, 371284731288835487, 371284731379158036]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 33930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 33900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362513896741535246, 362513912877960138⟩, ⟨(-990873664232955519), (-990503406462015467)⟩, true⟩

def words04 : List Nat := [371284732337452075, 371284732864325768, 371284733601466772, 371284734339003506, 371284735025740614, 371284735026847066, 371284735618781478, 371284736299666651, 371284737518731948, 371284738379227788]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 33940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 33900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362502393892379561, 362502410038819656⟩, ⟨(-600215930799203260), (-599845332960347056)⟩, true⟩

def words05 : List Nat := [371284739237480014, 371284740096067245, 371284741591792094, 371284742656132244, 371284743984650474, 371284745313506121, 371284746347661941, 371284746348761299, 371284746747315361, 371284747268790495]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 33950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 33900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362501886403355465, 362501902559592950⟩, ⟨(-582941445011713633), (-582570514402865173)⟩, true⟩

def words06 : List Nat := [371284748656875817, 371284748889929756, 371284749121006798, 371284749352451226, 371284749848316820, 371284750001833868, 371284751021755628, 371284752042085901, 371284752999596483, 371284753505564430]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 33960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 33900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362517776161344167, 362517792327514111⟩, ⟨(-1122832364276466840), (-1122461096211080622)⟩, true⟩

def words07 : List Nat := [371284754228869818, 371284754952677593, 371284756406149064, 371284756705426081, 371284756843627870, 371284756982165160, 371284757830698748, 371284758360552963, 371284759333463878, 371284760306790440]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 33970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 33900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486826859926569, 362486843036022189⟩, ⟨(-71102503308922232), (-70730897919618182)⟩, true⟩

def words08 : List Nat := [371284761237200661, 371284761346302472, 371284761993919234, 371284762642092885, 371284763327446020, 371284763328546327, 371284762860295592, 371284762390971400, 371284762102193421, 371284762164676256]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 33980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 33900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471591383281955, 362471607569307407⟩, ⟨446949839325987301, 447321782280898335⟩, true⟩

def words09 : List Nat := [371284762864159840, 371284763564077873, 371284764258750882, 371284764259853204, 371284764032563030, 371284763968523619, 371284764703802546, 371284764704903585, 371284764478028089, 371284764092315669]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 33990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 33900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 33900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk339
