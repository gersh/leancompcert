import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk616A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk616B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk616A

def state06 : KState := ⟨⟨362489310185712905, 362489366050986391⟩, ⟨(-249411948433257903), (-247085217998910901)⟩, true⟩

def words05 : List Nat := [371285356805122921, 371285357277993548, 371285357749387281, 371285357936992956, 371285358098741039, 371285358261566287, 371285358686537662, 371285358761544682, 371285358828125492, 371285358895442386]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362508296938371413, 362508352822383116⟩, ⟨(-1420225708669367548), (-1417897822740909748)⟩, true⟩

def words06 : List Nat := [371285359210003728, 371285359405451382, 371285359666892475, 371285359929180045, 371285360150840549, 371285360152946050, 371285360387143935, 371285360637640455, 371285361125308771, 371285361500323463]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507744108013543, 362507800011092366⟩, ⟨(-1386084473573773739), (-1383755411680222533)⟩, true⟩

def words07 : List Nat := [371285361855970069, 371285362212340444, 371285362830989640, 371285363349386229, 371285363947963545, 371285364547307884, 371285365057161326, 371285365217064812, 371285365582213333, 371285365948549927]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362504993183655109, 362505049105360866⟩, ⟨(-1216379173710989159), (-1214048962810726575)⟩, true⟩

def words08 : List Nat := [371285366576766852, 371285366855273143, 371285367115532172, 371285367376507890, 371285367684566227, 371285367884072457, 371285368345711823, 371285368808221232, 371285369269139329, 371285369590313117]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362513214906814460, 362513270847440634⟩, ⟨(-1723640632524369968), (-1721309254329466064)⟩, true⟩

def words09 : List Nat := [371285370018354647, 371285370447419250, 371285370985814261, 371285371210708287, 371285371396967826, 371285371583886193, 371285371996509745, 371285372348494062, 371285372802087167, 371285373256569669]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk616B
