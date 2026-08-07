import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk616

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484578664732908, 362484634417090625⟩, ⟨41692488899436105, 44012260318692195⟩, true⟩

def state01 : KState := ⟨⟨362492802700933596, 362492858471951901⟩, ⟨(-464891475348574185), (-462570554340640219)⟩, true⟩

def words00 : List Nat := [371285349110627542, 371285349200538990, 371285349553307261, 371285349906894760, 371285350197804409, 371285350199893608, 371285350145845107, 371285350154815660, 371285350426381151, 371285350550406388]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494502287006799, 362494558077044862⟩, ⟨(-569581635495832470), (-567259542585697464)⟩, true⟩

def words01 : List Nat := [371285350623879619, 371285350698026561, 371285351035018399, 371285351280265160, 371285351603810296, 371285351928172151, 371285352216237695, 371285352218327337, 371285352304546318, 371285352456516379]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482515165713018, 362482570974372746⟩, ⟨169130156658208286, 171453397133456716⟩, true⟩

def words02 : List Nat := [371285352715734876, 371285352740000602, 371285352741578216, 371285352734342243, 371285352726294980, 371285352719213080, 371285352702886354, 371285352828073629, 371285352951718128, 371285352953881646]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499334870828190, 362499390698396357⟩, ⟨(-867564462548855501), (-865240056652636669)⟩, true⟩

def words03 : List Nat := [371285353128537270, 371285353349462699, 371285353645954513, 371285353648044811, 371285353593833772, 371285353466450374, 371285353472074902, 371285353476990755, 371285353706138230, 371285353936230711]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362498080296396177, 362498136142871224⟩, ⟨(-790213625555821509), (-787888054143049937)⟩, true⟩

def words04 : List Nat := [371285354165615425, 371285354242937599, 371285354582963086, 371285354924054682, 371285355343272420, 371285355512071201, 371285355679527030, 371285355847710667, 371285356123362734, 371285356333068577]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk616
