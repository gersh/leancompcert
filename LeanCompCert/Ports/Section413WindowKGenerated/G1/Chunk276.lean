import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk276

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362450000557997768, 362450011039627963⟩, ⟨973858087540968700, 974053651745770206⟩, true⟩

def state01 : KState := ⟨⟨362431493611972474, 362431504101437135⟩, ⟨1484710454913919002, 1484906235390613676⟩, true⟩

def words00 : List Nat := [371285301560569494, 371285300832627244, 371285298603634952, 371285296374983657, 371285294146166397, 371285292314956297, 371285289912883264, 371285288464120142, 371285287015138952, 371285285565956897]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 27600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 27600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490009885351421, 362490020382746636⟩, ⟨(-131201594799538360), (-131005595319884864)⟩, true⟩

def words01 : List Nat := [371285283618726709, 371285282980630235, 371285282808092347, 371285282808971476, 371285281530354599, 371285279924273196, 371285278317939799, 371285278019946065, 371285277239287132, 371285277411988160]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 27610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 27600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362451859526061888, 362451870031408145⟩, ⟨922663831841292954, 922860050969724128⟩, true⟩

def words02 : List Nat := [371285277412658069, 371285277398428631, 371285276295434559, 371285276125782163, 371285275955706850, 371285275864809879, 371285274432235789, 371285272999854451, 371285271567238743, 371285270684718668]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 27620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 27600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362442908468677423, 362442918981953938⟩, ⟨1170185263350664083, 1170381701632279727⟩, true⟩

def words03 : List Nat := [371285269574228823, 371285269672916949, 371285269673575507, 371285269655793343, 371285268127341939, 371285266996851877, 371285265865981403, 371285265695043679, 371285264279327912, 371285262748293746]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 27630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 27600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470445363309104, 362470455884479385⟩, ⟨408938020602995175, 409134677107165627⟩, true⟩

def words04 : List Nat := [371285261216972900, 371285260838243181, 371285259943289022, 371285259172325514, 371285258401154460, 371285257401212888, 371285255003303146, 371285253911035896, 371285252818370218, 371285252798660476]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 27640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 27600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362472776117844087, 362472786647017395⟩, ⟨344604811961749545, 344801689791436229⟩, true⟩

def words05 : List Nat := [371285252264191322, 371285251718774002, 371285251931254002, 371285252237998351, 371285252941706542, 371285253645707412, 371285254098269131, 371285254099149713, 371285252812096954, 371285252362483463]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 27650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 27600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362452356337650933, 362452366874674532⟩, ⟨909585702461424810, 909782797469850618⟩, true⟩

def words06 : List Nat := [371285252680353164, 371285252681233916, 371285251710888843, 371285250741549783, 371285249771914475, 371285248860010654, 371285247466065277, 371285247225370174, 371285246984405447, 371285246628829569]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 27660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 27600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486160195378363, 362486170740389436⟩, ⟨(-26009441942829439), (-25812125881297575)⟩, true⟩

def words07 : List Nat := [371285245441200043, 371285244533545270, 371285244019290569, 371285244020171731, 371285242840595507, 371285241366506898, 371285239892169291, 371285239275579651, 371285238220389007, 371285238255078888]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 27670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 27600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362440543922874968, 362440554475831462⟩, ⟨1236717466596820450, 1236915002628732116⟩, true⟩

def words08 : List Nat := [371285238290006300, 371285238290887731, 371285236589452260, 371285235597040340, 371285234604277062, 371285233708369663, 371285231289231173, 371285228616916013, 371285225944429099, 371285224573434523]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 27680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 27600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362433535508758254, 362433546069660322⟩, ⟨1430962267063233146, 1431160023148757050⟩, true⟩

def words09 : List Nat := [371285222960870782, 371285222649621688, 371285222338096660, 371285221875815972, 371285219888519644, 371285218146676719, 371285216404492837, 371285215963221830, 371285214360787070, 371285212496488797]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 27690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 27600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 27600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk276
