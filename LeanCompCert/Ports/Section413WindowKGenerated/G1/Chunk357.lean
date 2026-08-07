import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk357

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492742912635901, 362492760830136742⟩, ⟨(-275361788977514801), (-274929491087691879)⟩, true⟩

def state01 : KState := ⟨⟨362465140798448623, 362465158726262792⟩, ⟨710218343798418468, 710651009929105362⟩, true⟩

def words00 : List Nat := [371285060732210009, 371285060733370210, 371285060481067389, 371285060232883890, 371285059984260793, 371285059883389233, 371285059505267429, 371285059452182936, 371285059398720265, 371285059342614770]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 35700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 35700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485356103425174, 362485374041744500⟩, ⟨(-11754404219638148), (-11321362898224332)⟩, true⟩

def words01 : List Nat := [371285058786137972, 371285058533055887, 371285058704625405, 371285058705806090, 371285058482085245, 371285058135935383, 371285057789351329, 371285057631920388, 371285057092977876, 371285057103167803]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 35710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 35700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362463714496574578, 362463732445392883⟩, ⟨761280853821733356, 761714270218886988⟩, true⟩

def words02 : List Nat := [371285057104059971, 371285056960622237, 371285055893637075, 371285055528734356, 371285055163286458, 371285055023595550, 371285053840162851, 371285052654194472, 371285051467773941, 371285051064766488]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 35720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 35700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362443342204580786, 362443360163828131⟩, ⟨1489450429664291686, 1489884218746147954⟩, true⟩

def words03 : List Nat := [371285050655058652, 371285050842443862, 371285051003957636, 371285051005122040, 371285050368990676, 371285049767964167, 371285049166364468, 371285049084973720, 371285048072626011, 371285046907497582]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 35730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 35700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477683504881205, 362477701474546336⟩, ⟨262001590851741293, 262435752317129939⟩, true⟩

def words04 : List Nat := [371285045741929398, 371285045241013449, 371285044504141752, 371285044421738437, 371285044338962033, 371285044135242255, 371285043017317925, 371285042682224421, 371285042346561235, 371285042334751011]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 35740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 35700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362494156832012707, 362494174812262461⟩, ⟨(-326992936103476473), (-326558396184025211)⟩, true⟩

def words05 : List Nat := [371285042130288964, 371285041835166975, 371285042025158391, 371285042142344348, 371285042497452102, 371285042852995701, 371285043133624053, 371285043134788800, 371285042864606332, 371285043121420930]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 35750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 35700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468313257381833, 362468331247994301⟩, ⟨597258767416495697, 597693677960746055⟩, true⟩

def words06 : List Nat := [371285043771191386, 371285043772353752, 371285043380780533, 371285042863837360, 371285042346490146, 371285041918023527, 371285041098532251, 371285040934992103, 371285040771055403, 371285040604381239]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 35760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 35700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501646152538918, 362501664153644256⟩, ⟨(-595158377740728025), (-594723091813888693)⟩, true⟩

def words07 : List Nat := [371285040452030265, 371285040767379657, 371285041778471928, 371285041914163223, 371285041928845609, 371285041943901621, 371285042153668635, 371285042154949663, 371285042489637988, 371285042955471654]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 35770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 35700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362461143953792241, 362461161965388514⟩, ⟨854121533578206132, 854557194923947188⟩, true⟩

def words08 : List Nat := [371285043417953164, 371285043419116259, 371285042841329766, 371285042657989438, 371285042474040259, 371285042349449331, 371285041384583524, 371285040399265048, 371285039413541520, 371285038947644003]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 35780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 35700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362456133598838667, 362456151620926195⟩, ⟨1033492482452177985, 1033928519334121825⟩, true⟩

def words09 : List Nat := [371285038281324692, 371285037938364909, 371285037595025316, 371285037116223058, 371285035942062086, 371285035006464054, 371285034070326382, 371285033914462766, 371285033111250649, 371285032305823797]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 35790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 35700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 35700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk357
