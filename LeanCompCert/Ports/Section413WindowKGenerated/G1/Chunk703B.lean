import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk703A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk703B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk703A

def state06 : KState := ⟨⟨362466251841824245, 362466325340944355⟩, ⟨1332516003327296752, 1336008556759964572⟩, true⟩

def words05 : List Nat := [371285314044104693, 371285314156358758, 371285314267424526, 371285314269835883, 371285314161017978, 371285314114994332, 371285314067749702, 371285314051533375, 371285313791103577, 371285313523956862]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469945461315387, 362470018982008039⟩, ⟨1072662165005553960, 1076156236392994628⟩, true⟩

def words06 : List Nat := [371285313255723359, 371285313163452531, 371285312970408249, 371285312907142960, 371285312843104943, 371285312747234557, 371285312400121295, 371285312159242233, 371285311917093472, 371285311809013766]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485229998062911, 362485303540731865⟩, ⟨(-3010525366802334), 485092600179938⟩, true⟩

def words07 : List Nat := [371285311593546750, 371285311342196199, 371285311089893548, 371285311040139196, 371285310896099004, 371285310807678234, 371285310718418948, 371285310630258034, 371285310430309417, 371285310433209845]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478049640517707, 362478123204631496⟩, ⟨502430579567175146, 505927706934457838⟩, true⟩

def words08 : List Nat := [371285310636122801, 371285310647187655, 371285310648991064, 371285310642556580, 371285310635195945, 371285310637156637, 371285310601091654, 371285310667676335, 371285310696196938, 371285310698692222]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489092325634048, 362489165911611272⟩, ⟨(-274869010972946986), (-271370344532691958)⟩, true⟩

def words09 : List Nat := [371285310665680944, 371285310736096975, 371285311006607134, 371285311036833087, 371285311059024138, 371285311081930575, 371285311170759222, 371285311173440664, 371285311216451453, 371285311273970718]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk703B
