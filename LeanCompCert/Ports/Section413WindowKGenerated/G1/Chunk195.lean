import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk195

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362451400754461060, 362451405834230489⟩, ⟨664777210177581694, 664844206079268158⟩, true⟩

def state01 : KState := ⟨⟨362447311933446631, 362447317018595672⟩, ⟨744724329172329288, 744791430004762550⟩, true⟩

def words00 : List Nat := [371285499532451597, 371285499533065889, 371285498300297626, 371285496650709733, 371285495001052025, 371285493966497631, 371285491889281280, 371285492160545719, 371285492161005098, 371285491874054656]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 19500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 19500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362516456389351424, 362516461479969413⟩, ⟨(-604622302931793599), (-604555095373082377)⟩, true⟩

def words01 : List Nat := [371285490289328287, 371285490661468134, 371285492156506485, 371285492157114580, 371285491308761990, 371285490030804398, 371285489447355614, 371285489448020891, 371285490419068801, 371285492006306533]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 19510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 19500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362458086967959808, 362458092064039594⟩, ⟨534851107496721292, 534918421697441524⟩, true⟩

def words02 : List Nat := [371285493558929541, 371285493559534204, 371285492126909124, 371285491799228520, 371285491471294109, 371285491187949483, 371285488417987332, 371285485472703599, 371285482527471417, 371285481640163375]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 19520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 19500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362401448989517520, 362401454091032988⟩, ⟨1641564656569250418, 1641632076956817788⟩, true⟩

def words03 : List Nat := [371285481448768614, 371285482659855093, 371285483518347570, 371285483518952351, 371285480891258682, 371285479065693620, 371285477239997665, 371285476519338221, 371285472314268980, 371285468015135180]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 19530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 19500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362466515875017271, 362466520981944751⟩, ⟨369982192852810790, 370049719018818050⟩, true⟩

def words04 : List Nat := [371285463716179348, 371285462027667113, 371285459031958678, 371285458646434721, 371285458260745810, 371285457448622356, 371285453827609749, 371285451553139924, 371285449355689806, 371285449356319116]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 19540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 19500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362516582303788012, 362516587416240455⟩, ⟨(-609145414432348202), (-609077780225310316)⟩, true⟩

def words05 : List Nat := [371285448388626802, 371285446894542170, 371285446512952325, 371285446513618637, 371285446928235817, 371285447535583236, 371285447890118656, 371285447890738467, 371285448469667456, 371285450062310426]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 19550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 19500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362463171411946755, 362463176529789793⟩, ⟨435927535759109773, 435995275434415711⟩, true⟩

def words06 : List Nat := [371285453811287229, 371285454084116532, 371285454361727480, 371285454639508620, 371285454930148809, 371285454930821705, 371285454570306757, 371285455213586980, 371285455286209961, 371285455286838052]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 19560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 19500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362518479411410529, 362518484534730014⟩, ⟨(-646666589755834492), (-646598742878821400)⟩, true⟩

def words07 : List Nat := [371285455612189447, 371285457076064992, 371285459962119915, 371285459962725924, 371285459376969403, 371285458329700012, 371285458834598237, 371285459417800047, 371285461104894823, 371285462792077503]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 19570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 19500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495374781912696, 362495379910698317⟩, ⟨(-194322511717811255), (-194254557786502119)⟩, true⟩

def words08 : List Nat := [371285464282396438, 371285464283002793, 371285462923616578, 371285463543679090, 371285464963693125, 371285464964309964, 371285464218449205, 371285463478311170, 371285463903994840, 371285464410836825]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 19580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 19500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362444478110183158, 362444483244443087⟩, ⟨803049511222475244, 803117572422687906⟩, true⟩

def words09 : List Nat := [371285465582859456, 371285466755009565, 371285467428323965, 371285467428930821, 371285465002177555, 371285463377386784, 371285462721742314, 371285462722349543, 371285460720776977, 371285458630791184]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 19590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 19500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 19500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk195
