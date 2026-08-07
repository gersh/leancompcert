import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk600

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496051130465483, 362496103914161724⟩, ⟨(-658473698172781565), (-656334432942814035)⟩, true⟩

def state01 : KState := ⟨⟨362487394560028772, 362487447361807209⟩, ⟨(-139016760885907356), (-136876410630361474)⟩, true⟩

def words00 : List Nat := [371285165577953889, 371285165681530371, 371285165769428427, 371285165858013890, 371285165960619835, 371285165962857917, 371285166116476875, 371285166292914486, 371285166466337573, 371285166506453518]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362513423333819910, 362513476153956877⟩, ⟨(-1701163994844176803), (-1699022542798971593)⟩, true⟩

def words01 : List Nat := [371285166659146715, 371285166812863213, 371285167243565969, 371285167352887780, 371285167419013993, 371285167485813527, 371285167829769296, 371285168072160562, 371285168545183343, 371285169019074104]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362493712452538032, 362493765291008459⟩, ⟨(-518077789165370549), (-515935236655540287)⟩, true⟩

def words02 : List Nat := [371285169485698638, 371285169582670188, 371285169936375166, 371285170291140057, 371285170658616136, 371285170660647788, 371285170658122803, 371285170568903965, 371285170665365043, 371285170810878934]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495793028712169, 362495845885520671⟩, ⟨(-642917801559586530), (-640774148122079486)⟩, true⟩

def words03 : List Nat := [371285171201260365, 371285171592523160, 371285171982121163, 371285172107511714, 371285172315795820, 371285172525054968, 371285173011079179, 371285173249730063, 371285173429048880, 371285173609107519]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362505502406522810, 362505555281526033⟩, ⟨(-1225822942550857228), (-1223678196609560756)⟩, true⟩

def words04 : List Nat := [371285174066013181, 371285174385583419, 371285174936050524, 371285175487313121, 371285175995231934, 371285176274176721, 371285176689937270, 371285177106781717, 371285177624189131, 371285177965634382]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491249565223767, 362491302458746516⟩, ⟨(-369844801479496369), (-367698943349495935)⟩, true⟩

def words05 : List Nat := [371285178276605198, 371285178588232316, 371285178970589234, 371285179215683362, 371285179543400644, 371285179871903054, 371285180200216174, 371285180202248835, 371285180262650766, 371285180367150481]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 60050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 60000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474098226308254, 362474151137908287⟩, ⟨660377277812124135, 662524221758968033⟩, true⟩

def words06 : List Nat := [371285180644016613, 371285180646050184, 371285180591366881, 371285180536415511, 371285180480659650, 371285180474234113, 371285180355952103, 371285180351497353, 371285180346374884, 371285180340867485]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 60000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501195989071803, 362501248919074437⟩, ⟨(-967569116628279054), (-965421067144890832)⟩, true⟩

def words07 : List Nat := [371285180158653961, 371285180075483236, 371285180088124294, 371285180090193754, 371285179960948370, 371285179781843047, 371285179698128452, 371285179722035277, 371285179990878332, 371285180260644237]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 60070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 60000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362500670941362856, 362500723889732964⟩, ⟨(-936075491109692159), (-933926338013556283)⟩, true⟩

def words08 : List Nat := [371285180479098269, 371285180481145913, 371285180698712567, 371285180947952908, 371285181266914640, 371285181322242869, 371285181376039518, 371285181430580858, 371285181761634878, 371285182022597893]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 60080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 60000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478048170420924, 362478101137078130⟩, ⟨423522502658940319, 425672754720195029⟩, true⟩

def words09 : List Nat := [371285182560000833, 371285183098195146, 371285183579026733, 371285183691075197, 371285183750149679, 371285183810228909, 371285184070271315, 371285184072305882, 371285183994003901, 371285183878421229]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 60090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 60000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 60000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk600
