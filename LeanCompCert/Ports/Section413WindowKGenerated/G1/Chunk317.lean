import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk317

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362507750973860803, 362507764962615923⟩, ⟨(-715081735924115566), (-714782005438353610)⟩, true⟩

def state01 : KState := ⟨⟨362476676135826550, 362476690133795572⟩, ⟨270066435399191953, 270366458013248959⟩, true⟩

def words00 : List Nat := [371285218060954840, 371285218061982406, 371285218223385311, 371285218508981451, 371285218866089119, 371285218867109957, 371285218051762691, 371285217230494827, 371285216408873900, 371285216354483471]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 31700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 31700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362430930784263100, 362430944791430409⟩, ⟨1721046166320773383, 1721346480659268425⟩, true⟩

def words01 : List Nat := [371285216556060106, 371285217026906996, 371285217355641656, 371285217356662884, 371285216480238079, 371285215911469613, 371285215342222340, 371285215039587195, 371285213414142905, 371285211704439844]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 31710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 31700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490128778399532, 362490142794711069⟩, ⟨(-156942749080136609), (-156642144640390365)⟩, true⟩

def words02 : List Nat := [371285209994376483, 371285209275212864, 371285208151218934, 371285208017993575, 371285207884450943, 371285207587570493, 371285206218792739, 371285205840761679, 371285206073051322, 371285206229691360]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 31720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 31700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483245333530562, 362483259359147373⟩, ⟨61510604481702101, 61811504225654609⟩, true⟩

def words03 : List Nat := [371285206230468644, 371285206187020246, 371285206761028879, 371285206963875299, 371285207180458621, 371285207397423180, 371285207535870890, 371285207536910557, 371285206851645484, 371285206791542637]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 31730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 31700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475933226505938, 362475947261224809⟩, ⟨293704552149062046, 294005740838773754⟩, true⟩

def words04 : List Nat := [371285207658924614, 371285207659946945, 371285207420599858, 371285207174254935, 371285206927532001, 371285206718464743, 371285206617193424, 371285206979454057, 371285207283498770, 371285207284558314]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 31740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 31700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362500284661817819, 362500298705806869⟩, ⟨(-479453852495567104), (-479152369432991076)⟩, true⟩

def words05 : List Nat := [371285207690907482, 371285208389429410, 371285210003013966, 371285210296981085, 371285210460450446, 371285210624220474, 371285211304258949, 371285211567393101, 371285212043138768, 371285212519306665]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 31750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 31700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487471406944780, 362487485460161763⟩, ⟨(-72582811302583071), (-72281035112609043)⟩, true⟩

def words06 : List Nat := [371285212988267225, 371285212989290231, 371285212138994423, 371285211988855215, 371285211992991194, 371285211994031989, 371285211327746341, 371285210664502681, 371285210324105644, 371285210396892977]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 31760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 31700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362449171328341208, 362449185390778028⟩, ⟨1144566740988041958, 1144868810138873216⟩, true⟩

def words07 : List Nat := [371285211456659362, 371285212516770731, 371285213278524592, 371285213279547923, 371285212723087814, 371285212302406348, 371285212270674666, 371285212271698057, 371285211344184561, 371285210211738975]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 31770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 31700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473527444143805, 362473541515737253⟩, ⟨370465973597818289, 370768333793172675⟩, true⟩

def words08 : List Nat := [371285209078900659, 371285208776859515, 371285207979054688, 371285207946116354, 371285207912855829, 371285207773093978, 371285206575265402, 371285205611615869, 371285204647498060, 371285204564928608]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 31780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 31700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504474039913009, 362504488120834892⟩, ⟨(-613464356428903241), (-613161699634620517)⟩, true⟩

def words09 : List Nat := [371285204198827981, 371285203836105154, 371285204095012361, 371285204362251162, 371285204935447930, 371285205508990767, 371285206076158178, 371285206077187104, 371285206305103000, 371285206912708273]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 31790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 31700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 31700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk317
