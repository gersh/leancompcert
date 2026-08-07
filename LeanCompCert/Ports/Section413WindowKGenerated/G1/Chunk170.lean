import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk170

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362570018843440212, 362570022657520727⟩, ⟨(-1441027768470744969), (-1440983910604143067)⟩, true⟩

def state01 : KState := ⟨⟨362512507745029179, 362512511563815308⟩, ⟨(-463327841488607584), (-463283903602766358)⟩, true⟩

def words00 : List Nat := [371285268882308786, 371285269277632707, 371285270958913972, 371285272640256603, 371285275099184187, 371285275099708207, 371285274493860419, 371285273872003026, 371285275590037359, 371285277191726497]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 17000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 17000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362439129268403260, 362439133091866544⟩, ⟨785592902902802398, 785636920371241120⟩, true⟩

def words01 : List Nat := [371285282246672389, 371285287301230185, 371285292252402347, 371285293354154038, 371285294999237723, 371285296644388175, 371285298002607094, 371285298003128156, 371285295434571055, 371285292722910683]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 17010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 17000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362511991035255186, 362511994863385562⟩, ⟨(-454797166348006093), (-454753069422312389)⟩, true⟩

def words02 : List Nat := [371285290750652124, 371285290751225700, 371285291246595731, 371285292719443823, 371285293449618047, 371285293450139257, 371285289590254073, 371285289179523700, 371285291805332080, 371285293373782937]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 17020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 17000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362533553458869521, 362533557291756569⟩, ⟨(-822038397958631534), (-821994220002535006)⟩, true⟩

def words03 : List Nat := [371285294241921424, 371285295110131194, 371285299424890895, 371285302380694484, 371285306353063533, 371285310325160436, 371285314270953919, 371285315362231070, 371285318193686977, 371285321025105403]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 17030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 17000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362522055791291780, 362522059628822534⟩, ⟨(-626064264336439409), (-626020007227216987)⟩, true⟩

def words04 : List Nat := [371285327299269409, 371285328990770920, 371285330359818365, 371285331728872888, 371285333274199485, 371285333274779194, 371285336381260062, 371285339655081267, 371285342912311485, 371285345066202910]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 17040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 17000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362562081360555333, 362562085202802277⟩, ⟨(-1308644015829513401), (-1308599678285422955)⟩, true⟩

def words05 : List Nat := [371285348938328160, 371285352810272581, 371285360120292572, 371285362853613472, 371285364992212429, 371285367130728888, 371285371910470163, 371285374979790968, 371285379476647864, 371285383973197599]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 17050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 17000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362539698623745811, 362539702470703829⟩, ⟨(-926829239120997270), (-926784821182203346)⟩, true⟩

def words06 : List Nat := [371285387727944256, 371285387981865789, 371285391232353520, 371285394482739921, 371285398745874814, 371285400909545765, 371285403058963617, 371285405208302127, 371285409276132068, 371285412457161436]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 17060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 17000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495751676976634, 362495755528647525⟩, ⟨(-176232696202565701), (-176188197790874399)⟩, true⟩

def words07 : List Nat := [371285418366327130, 371285424275022418, 371285429499496154, 371285430159627530, 371285431910923024, 371285433662264081, 371285438840049971, 371285439455415085, 371285440059791574, 371285440664307564]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 17070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 17000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362466249158897250, 362466253015247861⟩, ⟨327977301492702080, 328021879857792582⟩, true⟩

def words08 : List Nat := [371285442904408685, 371285443974624580, 371285446785023906, 371285449595298863, 371285451340502785, 371285451341025803, 371285448528632625, 371285447146835199, 371285446805219059, 371285446805760313]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 17080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 17000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504704158602972, 362504708019718974⟩, ⟨(-329335001735383189), (-329290341905785393)⟩, true⟩

def words09 : List Nat := [371285445683120632, 371285444515414731, 371285445598955598, 371285446920565129, 371285448847563509, 371285450774538709, 371285452439264880, 371285452439788541, 371285451273929326, 371285452400637881]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 17090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 17000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 17000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk170
