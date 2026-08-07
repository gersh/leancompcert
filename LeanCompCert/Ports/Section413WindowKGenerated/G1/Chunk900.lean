import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk900

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362466240259934551, 362466362827882255⟩, ⟨1680110038177245950, 1687558087555714656⟩, true⟩

def state01 : KState := ⟨⟨362469496698647199, 362469619294529448⟩, ⟨1387043237532601452, 1394493801169384902⟩, true⟩

def words00 : List Nat := [371285113267090628, 371285113185282807, 371285112992106192, 371285112796283678, 371285112599291677, 371285112432107729, 371285112218257435, 371285112129073782, 371285112038825947, 371285111948691979]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 90000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 90000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480342667173078, 362480465291459067⟩, ⟨410722023464685466, 418175143865538788⟩, true⟩

def words01 : List Nat := [371285111778701979, 371285111733677210, 371285111687093556, 371285111651310396, 371285111450355669, 371285111216381813, 371285110981086911, 371285110870496046, 371285110697688866, 371285110649644643]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 90010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 90000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474245531447725, 362474368184045203⟩, ⟨959596496208749423, 967052165351922727⟩, true⟩

def words02 : List Nat := [371285110600390337, 371285110539238668, 371285110379210631, 371285110344193298, 371285110307579199, 371285110295452213, 371285110118165086, 371285109915644017, 371285109711876762, 371285109627623477]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 90020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 90000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477608911724918, 362477731592632834⟩, ⟨656819833054144649, 664278051130130433⟩, true⟩

def words03 : List Nat := [371285109514435655, 371285109521885574, 371285109528103668, 371285109531300417, 371285109448961390, 371285109374930845, 371285109335642560, 371285109338798946, 371285109259318841, 371285109180939477]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 90030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 90000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482328462233488, 362482451171311388⟩, ⟨231860729311809738, 239321483952503306⟩, true⟩

def words04 : List Nat := [371285109101175865, 371285109057654558, 371285108965468107, 371285108977170691, 371285108979632754, 371285108957146173, 371285108823198093, 371285108797726185, 371285108819181652, 371285108822438013]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 90040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 90000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362484787955073069, 362484910692708134⟩, ⟨10382982897763328, 17846309257561994⟩, true⟩

def words05 : List Nat := [371285108795284893, 371285108767500742, 371285108830531075, 371285108864331293, 371285108907195997, 371285108951251115, 371285108971407552, 371285108974551204, 371285108851260253, 371285108852926406]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486679121158880, 362486801886824547⟩, ⟨(-159907125842704959), (-152441274901627491)⟩, true⟩

def words06 : List Nat := [371285108965345086, 371285108979461023, 371285108993048452, 371285109007732851, 371285109058860532, 371285109062333094, 371285109183597237, 371285109308167873, 371285109407997643, 371285109430041547]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498624393005362, 362498747187116786⟩, ⟨(-1235834348380285485), (-1228365935187247039)⟩, true⟩

def words07 : List Nat := [371285109574150863, 371285109719955002, 371285109987243540, 371285110122042981, 371285110236947511, 371285110352855963, 371285110526926899, 371285110640850669, 371285110794383630, 371285110949339816]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487565640793193, 362487688463319719⟩, ⟨(-239673001793684063), (-232202028827547977)⟩, true⟩

def words08 : List Nat := [371285111103415909, 371285111111660919, 371285111140183963, 371285111170259518, 371285111225785046, 371285111228930603, 371285111145006206, 371285111062031448, 371285111014496697, 371285111046831640]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474577026050037, 362474699876812208⟩, ⟨930580402337442027, 938053919195999165⟩, true⟩

def words09 : List Nat := [371285111166057193, 371285111286528606, 371285111397580523, 371285111400724030, 371285111360937963, 371285111344451879, 371285111345201373, 371285111348351671, 371285111242114046, 371285111130077425]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk900
