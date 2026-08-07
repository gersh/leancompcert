import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk063

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362560775831358341, 362560776309374928⟩, ⟨(-519954553283548866), (-519952513513426962)⟩, true⟩

def state01 : KState := ⟨⟨362388322117730221, 362388322597321182⟩, ⟨567985426606406247, 567987476303413459⟩, true⟩

def words00 : List Nat := [371278295503687251, 371278307750541083, 371278315561949453, 371278323370940878, 371278333949416046, 371278333949610623, 371278333520847016, 371278334978444617, 371278336460260590, 371278336460443752]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 6300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 6300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362782452510318670, 362782452991513115⟩, ⟨(-1920788257542976793), (-1920786197719823713)⟩, true⟩

def words01 : List Nat := [371278333045674740, 371278343890572261, 371278373592012254, 371278390586622512, 371278403551909802, 371278416513145666, 371278454530165705, 371278483027950295, 371278531124584200, 371278579206080459]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 6310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 6300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362622446447982288, 362622446930778826⟩, ⟨(-909243985986848352), (-909241916030211344)⟩, true⟩

def words02 : List Nat := [371278621739640819, 371278638935991832, 371278681144520617, 371278723339792552, 371278763328002287, 371278770103650035, 371278774018507364, 371278777932190498, 371278806817459826, 371278829506038626]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 6320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 6300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469506144473132, 362469506628868385⟩, ⟨60147078842979223, 60149158927680591⟩, true⟩

def words03 : List Nat := [371278868337986245, 371278907157740216, 371278945801388741, 371278951320247518, 371278958157995256, 371278964993675630, 371278996728876332, 371278996729054311, 371278995374360297, 371278993877910606]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 6330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 6300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362529342873902806, 362529343359894236⟩, ⟨(-318767475661062535), (-318765385448434827)⟩, true⟩

def words04 : List Nat := [371279005890746385, 371279010503562032, 371279039955486466, 371279069398201787, 371279094742872112, 371279095615037744, 371279108461609984, 371279121304224382, 371279144086410628, 371279151990747892]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 6340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 6300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362665950525407013, 362665951013024931⟩, ⟨(-1186993637244476442), (-1186991536695383578)⟩, true⟩

def words05 : List Nat := [371279158721775843, 371279165450746819, 371279196944372800, 371279216233898074, 371279238897510707, 371279261554062441, 371279283161934585, 371279287773698364, 371279317123385698, 371279346463945324]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 6350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 6300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362613285601282262, 362613286090493233⟩, ⟨(-851747601775794625), (-851745491086544677)⟩, true⟩

def words06 : List Nat := [371279400526829595, 371279421727899509, 371279437059779945, 371279452386897974, 371279472510101238, 371279480426034860, 371279513036969345, 371279545637737915, 371279574082284468, 371279595070074689]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 6360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 6300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362770991744707417, 362770992235531148⟩, ⟨(-1857108799974358370), (-1857106679003543870)⟩, true⟩

def words07 : List Nat := [371279632963748476, 371279670845621997, 371279733372239377, 371279763145020820, 371279786498770792, 371279809845252906, 371279843024147976, 371279864052264351, 371279909683762748, 371279955301037567]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 6370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 6300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362660228113210610, 362660228605650439⟩, ⟨(-1150574832707288561), (-1150572701417584911)⟩, true⟩

def words08 : List Nat := [371280000900809768, 371280013833413026, 371280042651092971, 371280071459843838, 371280107404129810, 371280117145965062, 371280126686419731, 371280136223946563, 371280170279714339, 371280198453652695]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 6380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 6300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362591144235888829, 362591144729947505⟩, ⟨(-708807902442371774), (-708805760800057406)⟩, true⟩

def words09 : List Nat := [371280229495753064, 371280260528213846, 371280291356219199, 371280296863770310, 371280309520096465, 371280322172552654, 371280359287431683, 371280376521950314, 371280393829618433, 371280411131947184]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 6390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 6300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 6300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk063
