import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk600A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk600B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk600A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk600B
