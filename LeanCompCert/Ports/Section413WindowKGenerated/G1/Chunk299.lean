import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk299

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504538369884255, 362504550754103883⟩, ⟨(-566151033318963158), (-565900737824793480)⟩, true⟩

def state01 : KState := ⟨⟨362465948698148271, 362465961091009589⟩, ⟨587789722890637306, 588040276815834990⟩, true⟩

def words00 : List Nat := [371285625579807414, 371285625580765611, 371285624731263262, 371285624594796298, 371285624661339896, 371285624662300223, 371285623716071518, 371285622756066473, 371285621795750092, 371285621414540711]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 29900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 29900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362447658450559630, 362447670852075227⟩, ⟨1134965269867780757, 1135216082686112865⟩, true⟩

def words01 : List Nat := [371285620757908826, 371285620570878309, 371285620383533009, 371285620116318210, 371285618361998854, 371285616905406685, 371285615448415743, 371285615106081456, 371285613833116703, 371285612566068747]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 29910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 29900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362498377190809400, 362498389600895289⟩, ⟨(-382740193081250073), (-382489123796252597)⟩, true⟩

def words02 : List Nat := [371285611298656845, 371285611145734079, 371285610510042974, 371285610589656334, 371285610590420968, 371285610473368885, 371285609292646907, 371285609226148256, 371285610143711444, 371285610571668192]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 29920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 29900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362467968712035188, 362467981130858967⟩, ⟨527661105371596859, 527912436227203569⟩, true⟩

def words03 : List Nat := [371285610770089230, 371285610968824042, 371285612019165814, 371285612521244689, 371285613363731813, 371285614206541288, 371285614877371950, 371285614878331213, 371285614064524720, 371285613476758340]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 29930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 29900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475424325502118, 362475436752868778⟩, ⟨304495900274635485, 304747486948322741⟩, true⟩

def words04 : List Nat := [371285613284411780, 371285613285377634, 371285612683293438, 371285612099750332, 371285611515869433, 371285611224234460, 371285611103535112, 371285611599964194, 371285611960119740, 371285611961114132]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 29940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 29900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362508628467012268, 362508640903082320⟩, ⟨(-690181597456439506), (-689929750073840810)⟩, true⟩

def words05 : List Nat := [371285612225286703, 371285612829673337, 371285613543938609, 371285613544901138, 371285613120616556, 371285612508103350, 371285612111598588, 371285612112656159, 371285612539157767, 371285613308874055]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 29950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 29900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362461594177924432, 362461606622662185⟩, ⟨719132855357631958, 719384962468646872⟩, true⟩

def words06 : List Nat := [371285614064452438, 371285614065412787, 371285613711366848, 371285613913533519, 371285614326105849, 371285614327066249, 371285613257758503, 371285611949622148, 371285610641172220, 371285610124913392]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 29960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 29900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362437372023452537, 362437384476824851⟩, ⟨1445240885925444328, 1445493251859353426⟩, true⟩

def words07 : List Nat := [371285609324677046, 371285608880638335, 371285608436314579, 371285607864194341, 371285606365304410, 371285604916194861, 371285603466678056, 371285602930922062, 371285601335952864, 371285599728721428]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 29970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 29900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487892393773260, 362487904855763734⟩, ⟨(-69593773511049430), (-69341149161626868)⟩, true⟩

def words08 : List Nat := [371285598121191632, 371285596979959188, 371285595419853105, 371285594970075492, 371285594520016211, 371285593883845543, 371285592572904214, 371285592250156797, 371285592712416248, 371285592790505436]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 29980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 29900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481869298604048, 362481881769353699⟩, ⟨111125067140203866, 111377954221540658⟩, true⟩

def words09 : List Nat := [371285592853639137, 371285592917098720, 371285593921480656, 371285594369151349, 371285594860725925, 371285595352614609, 371285595564323672, 371285595565285432, 371285594490381130, 371285594367827751]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 29990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 29900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 29900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk299
