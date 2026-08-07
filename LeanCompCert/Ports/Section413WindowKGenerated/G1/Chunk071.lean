import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk071

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362535409122169745, 362535409736325917⟩, ⟨(-351430002883257827), (-351427049766454777)⟩, true⟩

def state01 : KState := ⟨⟨362535314606182936, 362535315222157482⟩, ⟨(-351240710650993506), (-351237744614536410)⟩, true⟩

def words00 : List Nat := [371285926638060593, 371285926638262102, 371285916758887568, 371285921726225618, 371285925844941292, 371285925845145065, 371285919497176273, 371285911299205564, 371285914695257230, 371285921642546382]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 7100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 7100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362336915634055211, 362336916251848561⟩, ⟨1061045915266932788, 1061048894244480948⟩, true⟩

def words01 : List Nat := [371285941032718026, 371285960417523679, 371285979698493011, 371285979698694782, 371285972702419576, 371285971307021988, 371285978527890456, 371285978528092357, 371285960905959510, 371285939972950314]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 7110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 7100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362578764603701783, 362578765223303905⟩, ⟨(-662012199446994028), (-662009207581926810)⟩, true⟩

def words02 : List Nat := [371285919045728961, 371285917822396979, 371285907653248021, 371285908474050086, 371285908474206984, 371285907270286851, 371285892368723448, 371285894755413020, 371285916806883656, 371285929827485377]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 7120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 7100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362517143033790023, 362517143655235598⟩, ⟨(-222024278150877842), (-222021273132669636)⟩, true⟩

def words03 : List Nat := [371285942766833992, 371285955702620562, 371285976554546003, 371285990202154713, 371286009460376609, 371286028713281330, 371286046942247804, 371286046942450455, 371286048238578038, 371286052593320927]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 7130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 7100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362431284976000502, 362431285599250536⟩, ⟨391422712055994895, 391425729967458535⟩, true⟩

def words04 : List Nat := [371286071773722537, 371286071773925365, 371286064894121825, 371286057988247433, 371286051084226858, 371286049816384214, 371286039013315020, 371286036159102438, 371286033305622151, 371286030456588643]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 7140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 7100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362694451857259489, 362694452482342315⟩, ⟨(-1491409118259850465), (-1491406087234510815)⟩, true⟩

def words05 : List Nat := [371286034656148504, 371286046508053025, 371286071773162832, 371286082346500518, 371286089898478308, 371286097448405188, 371286116810517463, 371286126446602099, 371286155542555112, 371286184630473231]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 7150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 7100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362449063826358537, 362449064453276794⟩, ⟨266112327606176619, 266115371782559537⟩, true⟩

def words06 : List Nat := [371286208646843690, 371286208647046910, 371286211437745521, 371286216113896318, 371286226412157726, 371286226412361054, 371286210840416705, 371286195299499068, 371286179762828574, 371286179567890820]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 7160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 7100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362391018894505917, 362391019523253533⟩, ⟨683051036970015216, 683054094272271220⟩, true⟩

def words07 : List Nat := [371286184101998181, 371286193809203621, 371286203304585001, 371286203304789159, 371286193606008344, 371286182268683890, 371286178949970284, 371286178950174111, 371286165656788311, 371286152405464156]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 7170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 7100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362408452353105049, 362408452983678991⟩, ⟨558454945357093185, 558458015781772753⟩, true⟩

def words08 : List Nat := [371286140783421506, 371286140783652199, 371286143008443550, 371286149076457475, 371286152246690647, 371286152246894577, 371286129706010370, 371286126458931457, 371286124473840856, 371286124474051978]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 7180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 7100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362465609452397560, 362465610084834881⟩, ⟨147438759977213515, 147441843808681815⟩, true⟩

def words09 : List Nat := [371286113672997948, 371286100108927479, 371286092259732690, 371286092259958773, 371286096895085926, 371286102015149370, 371286107195549284, 371286107195753737, 371286090963006038, 371286088118697198]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 7190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 7100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 7100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk071
